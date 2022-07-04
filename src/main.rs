#![feature(box_syntax)]

use std::io::stdin;
use itertools::{put_back, Itertools, PutBack};
use nom::branch::alt;
use nom::bytes::complete::{tag, tag_no_case, take_while, take_while1};
use nom::character::complete::{anychar, char};
use nom::combinator::{all_consuming, map, opt, recognize};
use nom::error::{Error, ErrorKind};
use nom::multi::many0;
use nom::sequence::{preceded, terminated, tuple};
use nom::{Err, IResult};
use std::str::FromStr;
use eyre::eyre;

macro_rules! extract {
    ($item:ident in $expression:expr, $pattern:pat_param $( if $guard: expr )? $(,)?) => {
        match $expression {
            $pattern $( if $guard )? => $item,
            _ => panic!("Not Found"),
        }
    };
}

fn main() -> eyre::Result<()> {
    color_eyre::install()?;

    let mut buffer = String::new();
    loop {
        stdin().read_line(&mut buffer)?;
        let (_, tokens) = lex(&buffer).unwrap();
        println!("{:?}", &tokens);
        let ast = parse(&tokens)?;
        println!("{:?}", ast);
        let res = eval(ast);
        println!("{:?}", res);

        buffer.clear();
    }

    Ok(())
}

fn eval(root: Node) -> f64 {
    match root {
        Node::Numeric(num) => num,
        Node::Add(n1, n2) => eval(*n1) + eval(*n2),
        Node::Sub(n1, n2) => eval(*n1) - eval(*n2),
        Node::Mul(n1, n2) => eval(*n1) * eval(*n2),
        Node::Div(n1, n2) => eval(*n1) / eval(*n2),
    }
}

struct SliceWindowIter<'a, T> {
    slice: &'a [T],
    index: usize,
}

impl<'a, T> SliceWindowIter<'a, T> {
    pub fn new(slice: &'a [T]) -> Self {
        Self { slice, index: 0 }
    }

    pub fn go_back(&mut self) -> bool {
        if self.index != 0 {
            self.index -= 1;
            true
        } else {
            false
        }
    }

    pub fn right_side(&self) -> &'a [T] {
        &self.slice[self.index..]
    }

    pub fn advance_till(&mut self, mut f: impl FnMut(&'a T) -> bool) -> &'a [T] {
        for i in self.index..self.slice.len() {
            if f(&self.slice[i]) {
                let li = self.index;
                self.index = i + 1;
                return &self.slice[li..i];
            }
        }
        &[]
    }
}

impl<'a, T: Clone> Iterator for SliceWindowIter<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.slice.len() - self.index == 0 {
            return None;
        }
        self.index += 1;
        Some(self.slice[self.index - 1].clone())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.slice.len() - self.index;
        (size, Some(size))
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.slice.len() - self.index
    }
}

enum ParsingState {
    Init,
    Num(f64),
    Sign(bool),
    Node(Node),
    Intent(IntentFn),
}

fn par_end_finder() -> impl FnMut(&Token) -> bool {
    let mut open = 0;
    move |t| {
        match t {
            Token::ParenOpen => open += 1,
            Token::ParenClose if open == 0 => return true,
            Token::ParenClose => open -= 1,
            _ => (),
        }
        false
    }
}

fn parse(tokens: &[Token]) -> eyre::Result<Node> {
    let mut state = ParsingState::Init;
    let mut tokens = SliceWindowIter::new(tokens);

    while let Some(tk) = tokens.next() {
        state = match state {
            ParsingState::Init => match tk {
                Token::Numeric(num) => ParsingState::Num(num),
                Token::Add => ParsingState::Sign(false),
                Token::Sub => ParsingState::Sign(true),
                Token::Mul => return Err(eyre!("mul not supported at start")),
                Token::Div => return Err(eyre!("div not supported at start")),
                Token::ParenOpen => {
                    let window = tokens.advance_till(par_end_finder());
                    ParsingState::Node(parse(window)?)
                }
                Token::ParenClose => return Err(eyre!("found unwanted closing parenthesis")),
            },
            ParsingState::Sign(sign) => match tk {
                Token::Numeric(num) => ParsingState::Num(if sign { -num } else { num }),
                Token::Add | Token::Sub | Token::Mul | Token::Div => {
                    return Err(eyre!("unexpected operator"))
                }
                Token::ParenOpen => {
                    let window = tokens.advance_till(par_end_finder());
                    let right = parse(window)?;
                    ParsingState::Node(if sign {
                        Node::Sub(box Node::Numeric(0.0), box right)
                    } else {
                        right
                    })
                }
                Token::ParenClose => return Err(eyre!("found unwanted closing parenthesis")),
            },
            ParsingState::Num(num) => match tk {
                Token::Numeric(_) => return Err(eyre!("missing operator")),
                Token::Add => {
                    ParsingState::Intent(intent(Node::Add, Node::Numeric(num)))
                }
                Token::Sub => {
                    ParsingState::Intent(intent(Node::Sub, Node::Numeric(num)))
                }
                Token::Mul => {
                    ParsingState::Intent(intent(Node::Mul, Node::Numeric(num)))
                }
                Token::Div => {
                    ParsingState::Intent(intent(Node::Div, Node::Numeric(num)))
                }
                Token::ParenOpen => {
                    let window = tokens.advance_till(par_end_finder());
                    let right = parse(window)?;
                    ParsingState::Node(content(Node::Mul, Node::Numeric(num), right))
                }
                Token::ParenClose => return Err(eyre!("found unwanted closing parenthesis")),
            }
            ParsingState::Node(node) => match tk {
                Token::Numeric(num) => ParsingState::Node(content(Node::Mul, node, Node::Numeric(num))),
                Token::Add => ParsingState::Intent(intent(Node::Add, node)),
                Token::Sub => ParsingState::Intent(intent(Node::Sub, node)),
                Token::Mul => ParsingState::Intent(intent(Node::Mul, node)),
                Token::Div => ParsingState::Intent(intent(Node::Div, node)),
                Token::ParenOpen => {
                    let window = tokens.advance_till(par_end_finder());
                    let right = parse(window)?;
                    ParsingState::Node(content(Node::Mul, node, right))
                },
                Token::ParenClose => return Err(eyre!("found unwanted closing parenthesis")),
            }
            ParsingState::Intent(intent) => match tk {
                Token::Numeric(num) => ParsingState::Node(intent(Node::Numeric(num))),
                Token::Add | Token::Sub | Token::Mul | Token::Div => {
                    return Err(eyre!("unexpected operator"))
                }
                Token::ParenOpen => {
                    let window = tokens.advance_till(par_end_finder());
                    let right = parse(window)?;
                    ParsingState::Node(intent(right))
                },
                Token::ParenClose => return Err(eyre!("found unwanted closing parenthesis")),
            },
        }
    }

    Ok(match state {
        ParsingState::Num(num) => Node::Numeric(num),
        ParsingState::Node(node) => node,
        ParsingState::Init | ParsingState::Sign(_) | ParsingState::Intent(_) => return Err(eyre!("invalid state")),
    })
}


type BoxNode = Box<Node>;
type IntentFn = Box<dyn FnOnce(Node) -> Node + 'static>;

fn intent<F>(f: F, a: Node) -> IntentFn
    where
        F: 'static + Fn(BoxNode, BoxNode) -> Node
{
    box move |b: Node| content(f, a, b)
}

fn content<F>(f: F, a: Node, b: Node) -> Node
where
    F: 'static + Fn(BoxNode, BoxNode) -> Node
{
    f(box a, box b)
}


fn whitespaces(i: &str) -> IResult<&str, ()> {
    let (i, _) = take_while(char::is_whitespace)(i)?;
    Ok((i, ()))
}

fn lex(i: &str) -> IResult<&str, Vec<Token>> {
    all_consuming(terminated(many0(preceded(whitespaces, token)), whitespaces))(i)
}

fn token(i: &str) -> IResult<&str, Token> {
    alt((map(numeric, |float| Token::Numeric(float)), tiny_token))(i)
}

fn numeric(i: &str) -> IResult<&str, f64> {
    let (i, num) = recognize(numeric_sel)(i)?;

    let num = f64::from_str(num).map_err(|_| Err::Error(Error::new(num, ErrorKind::Float)))?;

    Ok((i, num))
}

fn numeric_sel(i: &str) -> IResult<&str, ()> {
    let (i, _first) = num_par(i)?;

    let (i, _) = opt(tuple((
        tag("."),
        num_par,
        opt(tuple((
            tag_no_case("e"),
            opt(alt((char('+'), char('-')))),
            num_par,
        ))),
    )))(i)?;

    Ok((i, ()))
}

fn num_par(i: &str) -> IResult<&str, ()> {
    map(take_while1(|c: char| c.is_ascii_digit()), |_| ())(i)
}

fn tiny_token(oi: &str) -> IResult<&str, Token> {
    let (i, c) = anychar(oi)?;
    Ok((
        i,
        match c {
            '+' => Token::Add,
            '-' => Token::Sub,
            '*' => Token::Mul,
            '/' => Token::Div,
            '(' => Token::ParenOpen,
            ')' => Token::ParenClose,
            _ => return Err(Err::Error(Error::new(oi, ErrorKind::Tag))),
        },
    ))
}

#[derive(Debug, Copy, Clone)]
enum Token {
    Numeric(f64),
    Add,
    Sub,
    Mul,
    Div,
    ParenOpen,
    ParenClose,
}

#[derive(Debug, Clone)]
enum Node {
    Numeric(f64),

    Add(BoxNode, BoxNode),
    Sub(BoxNode, BoxNode),
    Mul(BoxNode, BoxNode),
    Div(BoxNode, BoxNode),
}
