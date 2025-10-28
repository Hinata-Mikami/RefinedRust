// Based on the syn crate: https://github.com/dtolnay/syn
// Permission is hereby granted, free of charge, to any
// person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the
// Software without restriction, including without
// limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following
// conditions:
//
// The above copyright notice and this permission notice
// shall be included in all copies or substantial portions
// of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
// ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
// PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
// SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
// IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

/// This provides parsing facilities for rustc attribute token streams.
// TODO: refactor/ make into own crate?
use std::cell::Cell;
use std::{result, vec};

use ast::tokenstream::TokenStream;
use rr_rustc_interface::{ast, span};

#[derive(Debug)]
pub enum Error {
    EOF,
    WrongTokenKind(ast::token::TokenKind, ast::token::TokenKind, span::Span),
    UnexpectedDelim(ast::tokenstream::DelimSpan),
    ExpectedIdent(ast::token::TokenKind, span::Span),
    ExpectedLiteral(ast::token::TokenKind, span::Span),
    UnexpectedLitKind(ast::token::LitKind, ast::token::LitKind),
    OtherErr(span::Span, String),
}

pub type Result<T> = result::Result<T, Error>;

// TODO: maybe change to just have a shared reference to the vector? (or a RefCell)?
// we anyways only ever read from it, and making parse::Buffer Copy might be nice for
// having multiple different cursors at once into the same vector.
#[derive(Clone, Debug)]
pub struct Buffer {
    trees: Vec<ast::tokenstream::TokenTree>,
    index: Cell<usize>,
}

impl Buffer {
    #[must_use]
    pub fn new(stream: &TokenStream) -> Self {
        // TODO; maybe avoid the cloning
        let trees: Vec<ast::tokenstream::TokenTree> = stream.iter().cloned().collect();

        Self {
            trees,
            index: Cell::new(0),
        }
    }

    pub fn parse<U, T: Parse<U>>(&self, meta: &U) -> Result<T>
    where
        U: ?Sized,
    {
        T::parse(self, meta)
    }

    pub fn pos(&self) -> Option<span::Span> {
        self.trees.get(self.index.get()).map(ast::tokenstream::TokenTree::span)
    }

    fn peek(&self, n: usize) -> Result<&ast::tokenstream::TokenTree> {
        self.trees.get(self.index.get() + n).ok_or(Error::EOF)
    }

    fn advance(&self, n: usize) {
        self.index.set(self.index.get() + n);
    }

    const fn is_empty(&self) -> bool {
        self.index.get() >= self.trees.len()
    }

    /// Check if the next symbol is a token matching the given kind.
    fn peek_token(&self, token: &ast::token::TokenKind) -> bool {
        let tok = self.peek(0);

        match tok {
            Ok(ast::tokenstream::TokenTree::Token(tok, _)) => tok.kind == *token,
            _ => false,
        }
    }

    pub fn peek_delimited(&self) -> Option<&TokenStream> {
        let tok = self.peek(0);

        match tok {
            Ok(ast::tokenstream::TokenTree::Delimited(_, _, _, stream)) => Some(stream),
            _ => None,
        }
    }

    /// Consume a token of the given kind.
    fn expect_token(&self, token: ast::token::TokenKind) -> Result<span::Span> {
        let tok = self.peek(0)?;
        match tok {
            ast::tokenstream::TokenTree::Token(tok, _) => {
                if tok.kind == token {
                    self.advance(1);
                    Ok(tok.span)
                } else {
                    Err(Error::WrongTokenKind(token, tok.kind, tok.span))
                }
            },
            ast::tokenstream::TokenTree::Delimited(span, _, _, _) => Err(Error::UnexpectedDelim(*span)),
        }
    }

    /// Consume an identifier.
    fn expect_ident(&self) -> Result<span::Symbol> {
        let tok = self.peek(0)?;
        match tok {
            ast::tokenstream::TokenTree::Token(tok, _) => match tok.kind {
                ast::token::TokenKind::Ident(sym, _) => {
                    self.advance(1);
                    Ok(sym)
                },
                _ => Err(Error::ExpectedIdent(tok.kind, tok.span)),
            },
            ast::tokenstream::TokenTree::Delimited(span, _, _, _) => Err(Error::UnexpectedDelim(*span)),
        }
    }

    /// Consume a literal.
    fn expect_literal(&self) -> Result<(ast::token::Lit, span::Span)> {
        let tok = self.peek(0)?;
        match tok {
            ast::tokenstream::TokenTree::Token(tok, _) => match tok.kind {
                ast::token::TokenKind::Literal(lit) => {
                    self.advance(1);
                    Ok((lit, tok.span))
                },
                _ => Err(Error::ExpectedLiteral(tok.kind, tok.span)),
            },
            ast::tokenstream::TokenTree::Delimited(span, _, _, _) => Err(Error::UnexpectedDelim(*span)),
        }
    }
}

pub type Stream<'a> = &'a Buffer;

pub trait Parse<U>: Sized
where
    U: ?Sized,
{
    fn parse(stream: Stream<'_>, meta: &U) -> Result<Self>;
}

impl<U, T: Parse<U>> Parse<U> for Box<T>
where
    U: ?Sized,
{
    fn parse(stream: Stream<'_>, meta: &U) -> Result<Self> {
        stream.parse(meta).map(Self::new)
    }
}

pub trait Peek {
    fn peek(stream: Stream<'_>) -> bool;
}

pub trait PToken: Peek {}

macro_rules! define_punctuation_structs {
    ($($token:tt pub struct $name:ident/$len:tt #[$doc:meta])*) => {
        $(
            #[repr(C)]
            #[$doc]
            #[derive(Copy, Clone)]
            ///
            /// Don't try to remember the name of this type &mdash; use the
            /// [`MToken!`] macro instead.
            pub struct $name {
                pub span: span::Span,
            }
        )*
    };
}

macro_rules! define_punctuation {
    ($($token:tt pub struct $name:ident/$len:tt $tk:expr , #[$doc:meta])*) => {
        $(
            define_punctuation_structs! {
                $token pub struct $name/$len #[$doc]
            }

            impl<U> Parse<U> for $name where U: ?Sized {
                fn parse(input: Stream<'_>, _: &U) -> Result<Self> {
                    Ok($name {
                        span: input.expect_token($tk)?,
                    })
                }
            }

            impl Peek for $name {
                fn peek(input: Stream<'_>) -> bool {
                    input.peek_token(&$tk)
                }
            }

            impl PToken for $name {

            }
        )*
    };
}

define_punctuation! {
    "+"           pub struct Add/1              ast::token::TokenKind::Plus,         /// `+`
    "+="          pub struct AddEq/2            ast::token::TokenKind::PlusEq,       /// `+=`
    "&"           pub struct And/1              ast::token::TokenKind::And,          /// `&`
    "&&"          pub struct AndAnd/2           ast::token::TokenKind::AndAnd,       /// `&&`
    "&="          pub struct AndEq/2            ast::token::TokenKind::AndEq,        /// `&=`
    "@"           pub struct At/1               ast::token::TokenKind::At,           /// `@`
    "!"           pub struct Bang/1             ast::token::TokenKind::Bang,         /// `!`
    "^"           pub struct Caret/1            ast::token::TokenKind::Caret,        /// `^`
    "^="          pub struct CaretEq/2          ast::token::TokenKind::CaretEq,      /// `^=`
    ":"           pub struct Colon/1            ast::token::TokenKind::Colon,        /// `:`
    "::"          pub struct Colon2/2           ast::token::TokenKind::PathSep,      /// `::`
    ","           pub struct Comma/1            ast::token::TokenKind::Comma,        /// `,`
    "/"           pub struct Div/1              ast::token::TokenKind::Slash,        /// `/`
    "/="          pub struct DivEq/2            ast::token::TokenKind::SlashEq,      /// `/=`
    "$"           pub struct Dollar/1           ast::token::TokenKind::Dollar,       /// `$`
    "."           pub struct Dot/1              ast::token::TokenKind::Dot,          /// `.`
    ".."          pub struct Dot2/2             ast::token::TokenKind::DotDot,       /// `..`
    "..."         pub struct Dot3/3             ast::token::TokenKind::DotDotDot,    /// `...`
    "..="         pub struct DotDotEq/3         ast::token::TokenKind::DotDotEq,     /// `..=`
    "="           pub struct Eq/1               ast::token::TokenKind::Eq,           /// `=`
    "=="          pub struct EqEq/2             ast::token::TokenKind::EqEq,         /// `==`
    ">="          pub struct Ge/2               ast::token::TokenKind::Ge,           /// `>=`
    ">"           pub struct Gt/1               ast::token::TokenKind::Gt,           /// `>`
    "<="          pub struct Le/2               ast::token::TokenKind::Le,           /// `<=`
    "<"           pub struct Lt/1               ast::token::TokenKind::Lt,           /// `<`
    "*="          pub struct MulEq/2            ast::token::TokenKind::StarEq,       /// `*=`
    "!="          pub struct Ne/2               ast::token::TokenKind::Ne,           /// `!=`
    "|"           pub struct Or/1               ast::token::TokenKind::Or,           /// `|`
    "|="          pub struct OrEq/2             ast::token::TokenKind::OrEq,         /// `|=`
    "||"          pub struct OrOr/2             ast::token::TokenKind::OrOr,         /// `||`
    "#"           pub struct Pound/1            ast::token::TokenKind::Pound,        /// `#`
    "?"           pub struct Question/1         ast::token::TokenKind::Question,     /// `?`
    "->"          pub struct RArrow/2           ast::token::TokenKind::RArrow,       /// `->`
    "<-"          pub struct LArrow/2           ast::token::TokenKind::LArrow,       /// `<-`
    "%"           pub struct Rem/1              ast::token::TokenKind::Percent,      /// `%`
    "%="          pub struct RemEq/2            ast::token::TokenKind::PercentEq,    /// `%=`
    "=>"          pub struct FatArrow/2         ast::token::TokenKind::FatArrow,     /// `=>`
    ";"           pub struct Semi/1             ast::token::TokenKind::Semi,         /// `;`
    "<<"          pub struct Shl/2              ast::token::TokenKind::Shl,          /// `<<`
    "<<="         pub struct ShlEq/3            ast::token::TokenKind::ShlEq,        /// `<<=`
    ">>"          pub struct Shr/2              ast::token::TokenKind::Shr,          /// `>>`
    ">>="         pub struct ShrEq/3            ast::token::TokenKind::ShrEq,        /// `>>=`
    "*"           pub struct Star/1             ast::token::TokenKind::Star,         /// `*`
    "-"           pub struct Sub/1              ast::token::TokenKind::Minus,        /// `-`
    "-="          pub struct SubEq/2            ast::token::TokenKind::MinusEq,      /// `-=`
    "~"           pub struct Tilde/1            ast::token::TokenKind::Tilde,        /// `~`
}

#[macro_export]
macro_rules! MToken {
    [+]           => { $crate::parse::Add };
    [+=]          => { $crate::parse::AddEq };
    [&]           => { $crate::parse::And };
    [&&]          => { $crate::parse::AndAnd };
    [&=]          => { $crate::parse::AndEq };
    [@]           => { $crate::parse::At };
    [!]           => { $crate::parse::Bang };
    [^]           => { $crate::parse::Caret };
    [^=]          => { $crate::parse::CaretEq };
    [:]           => { $crate::parse::Colon };
    [::]          => { $crate::parse::Colon2 };
    [,]           => { $crate::parse::Comma };
    [/]           => { $crate::parse::Div };
    [/=]          => { $crate::parse::DivEq };
    [$]           => { $crate::parse::Dollar };
    [.]           => { $crate::parse::Dot };
    [..]          => { $crate::parse::Dot2 };
    [...]         => { $crate::parse::Dot3 };
    [..=]         => { $crate::parse::DotDotEq };
    [=]           => { $crate::parse::Eq };
    [==]          => { $crate::parse::EqEq };
    [>=]          => { $crate::parse::Ge };
    [>]           => { $crate::parse::Gt };
    [<=]          => { $crate::parse::Le };
    [<]           => { $crate::parse::Lt };
    [*=]          => { $crate::parse::MulEq };
    [!=]          => { $crate::parse::Ne };
    [|]           => { $crate::parse::Or };
    [|=]          => { $crate::parse::OrEq };
    [||]          => { $crate::parse::OrOr };
    [#]           => { $crate::parse::Pound };
    [?]           => { $crate::parse::Question };
    [->]          => { $crate::parse::RArrow };
    [<-]          => { $crate::parse::LArrow };
    [%]           => { $crate::parse::Rem };
    [%=]          => { $crate::parse::RemEq };
    [=>]          => { $crate::parse::FatArrow };
    [;]           => { $crate::parse::Semi };
    [<<]          => { $crate::parse::Shl };
    [<<=]         => { $crate::parse::ShlEq };
    [>>]          => { $crate::parse::Shr };
    [>>=]         => { $crate::parse::ShrEq };
    [*]           => { $crate::parse::Star };
    [-]           => { $crate::parse::Sub };
    [-=]          => { $crate::parse::SubEq };
    [~]           => { $crate::parse::Tilde };
    [_]           => { $crate::parse::Underscore };
}

#[derive(Copy, Clone)]
pub struct LitStr {
    sym: span::Symbol,
}

impl LitStr {
    #[must_use]
    pub fn value(self) -> String {
        self.sym.to_string()
    }
}

impl<U> Parse<U> for LitStr
where
    U: ?Sized,
{
    fn parse(stream: Stream<'_>, _: &U) -> Result<Self> {
        let lit = stream.expect_literal()?;
        match lit.0.kind {
            ast::token::LitKind::Str => Ok(Self { sym: lit.0.symbol }),
            _ => Err(Error::UnexpectedLitKind(ast::token::LitKind::Str, lit.0.kind)),
        }
    }
}

#[derive(Copy, Clone)]
pub struct Ident {
    sym: span::Symbol,
}

impl<U> Parse<U> for Ident
where
    U: ?Sized,
{
    fn parse(stream: Stream<'_>, _: &U) -> Result<Self> {
        let sym = stream.expect_ident()?;
        Ok(Self { sym })
    }
}

impl Ident {
    #[must_use]
    pub fn value(self) -> String {
        self.sym.to_string()
    }
}

pub struct Punctuated<T, P> {
    inner: Vec<(T, P)>,
    last: Option<Box<T>>,
}

impl<T, P> Punctuated<T, P> {
    /// Creates an empty punctuated sequence.
    #[must_use]
    const fn new() -> Self {
        Self {
            inner: Vec::new(),
            last: None,
        }
    }

    /// Determines whether this punctuated sequence is empty, meaning it
    /// contains no syntax tree nodes or punctuation.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.inner.len() == 0 && self.last.is_none()
    }

    /// Returns the number of syntax tree nodes in this punctuated sequence.
    ///
    /// This is the number of nodes of type `T`, not counting the punctuation of
    /// type `P`.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.len() + usize::from(self.last.is_some())
    }

    /// Returns an iterator over borrowed syntax tree nodes of type `&T`.
    fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: Box::new(PrivateIter {
                inner: self.inner.iter(),
                last: self.last.as_ref().map(Box::as_ref).into_iter(),
            }),
        }
    }

    /// Appends a syntax tree node onto the end of this punctuated sequence. The
    /// sequence must previously have a trailing punctuation.
    ///
    /// Use [`push`] instead if the punctuated sequence may or may not already
    /// have trailing punctuation.
    ///
    /// [`push`]: Punctuated::push
    ///
    /// # Panics
    ///
    /// Panics if the sequence does not already have a trailing punctuation when
    /// this method is called.
    fn push_value(&mut self, value: T) {
        assert!(
            self.empty_or_trailing(),
            "Punctuated::push_value: cannot push value if Punctuated is missing trailing punctuation",
        );

        self.last = Some(Box::new(value));
    }

    /// Appends a trailing punctuation onto the end of this punctuated sequence.
    /// The sequence must be non-empty and must not already have trailing
    /// punctuation.
    ///
    /// # Panics
    ///
    /// Panics if the sequence is empty or already has a trailing punctuation.
    fn push_punct(&mut self, punctuation: P) {
        assert!(
            self.last.is_some(),
            "Punctuated::push_punct: cannot push punctuation if Punctuated is empty or already has trailing punctuation",
        );

        let last = self.last.take().unwrap();
        self.inner.push((*last, punctuation));
    }

    /// Returns true if either this `Punctuated` is empty, or it has a trailing
    /// punctuation.
    ///
    /// Equivalent to `punctuated.is_empty() || punctuated.trailing_punct()`.
    #[must_use]
    const fn empty_or_trailing(&self) -> bool {
        self.last.is_none()
    }

    /// Appends a syntax tree node onto the end of this punctuated sequence.
    ///
    /// If there is not a trailing punctuation in this sequence when this method
    /// is called, the default value of punctuation type `P` is inserted before
    /// the given value of type `T`.
    fn push(&mut self, value: T)
    where
        P: Default,
    {
        if !self.empty_or_trailing() {
            self.push_punct(Default::default());
        }
        self.push_value(value);
    }

    /// Parses zero or more occurrences of `T` separated by punctuation of type
    /// `P`, with optional trailing punctuation.
    ///
    /// Parsing continues until the end of this parse stream. The entire content
    /// of this parse stream must consist of `T` and `P`.
    ///
    /// *This function is available only if Syn is built with the `"parsing"`
    /// feature.*
    pub fn parse_terminated<U>(input: Stream<'_>, meta: &U) -> Result<Self>
    where
        T: Parse<U>,
        P: Parse<U>,
        U: ?Sized,
    {
        Self::parse_terminated_with(input, T::parse, meta)
    }

    /// Parses zero or more occurrences of `T` using the given parse function,
    /// separated by punctuation of type `P`, with optional trailing
    /// punctuation.
    ///
    /// Like [`parse_terminated`], the entire content of this stream is expected
    /// to be parsed.
    ///
    /// [`parse_terminated`]: Punctuated::parse_terminated
    ///
    /// *This function is available only if Syn is built with the `"parsing"`
    /// feature.*
    fn parse_terminated_with<U>(
        input: Stream<'_>,
        parser: fn(Stream<'_>, &U) -> Result<T>,
        meta: &U,
    ) -> Result<Self>
    where
        P: Parse<U>,
        U: ?Sized,
    {
        let mut punctuated = Self::new();

        loop {
            if input.is_empty() {
                break;
            }
            let value = parser(input, meta)?;
            punctuated.push_value(value);
            if input.is_empty() {
                break;
            }
            let punct = input.parse(meta)?;
            punctuated.push_punct(punct);
        }

        Ok(punctuated)
    }

    /// Parses one or more occurrences of `T` separated by punctuation of type
    /// `P`, not accepting trailing punctuation.
    ///
    /// Parsing continues as long as punctuation `P` is present at the head of
    /// the stream. This method returns upon parsing a `T` and observing that it
    /// is not followed by a `P`, even if there are remaining tokens in the
    /// stream.
    ///
    /// *This function is available only if Syn is built with the `"parsing"`
    /// feature.*
    pub fn parse_separated_nonempty<U>(input: Stream<'_>, meta: &U) -> Result<Self>
    where
        T: Parse<U>,
        P: PToken + Parse<U>,
        U: ?Sized,
    {
        Self::parse_separated_nonempty_with(input, T::parse, meta)
    }

    /// Parses one or more occurrences of `T` using the given parse function,
    /// separated by punctuation of type `P`, not accepting trailing
    /// punctuation.
    ///
    /// Like [`parse_separated_nonempty`], may complete early without parsing
    /// the entire content of this stream.
    ///
    /// [`parse_separated_nonempty`]: Punctuated::parse_separated_nonempty
    ///
    /// *This function is available only if Syn is built with the `"parsing"`
    /// feature.*
    fn parse_separated_nonempty_with<U>(
        input: Stream<'_>,
        parser: fn(Stream<'_>, &U) -> Result<T>,
        meta: &U,
    ) -> Result<Self>
    where
        P: Peek + Parse<U>,
        U: ?Sized,
    {
        let mut punctuated = Self::new();

        loop {
            let value = parser(input, meta)?;
            punctuated.push_value(value);
            if !P::peek(input) {
                break;
            }
            let punct = input.parse(meta)?;
            punctuated.push_punct(punct);
        }

        Ok(punctuated)
    }
}

impl<T, P> FromIterator<T> for Punctuated<T, P>
where
    P: Default,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut ret = Self::new();
        ret.extend(iter);
        ret
    }
}

impl<T, P> Extend<T> for Punctuated<T, P>
where
    P: Default,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.push(value);
        }
    }
}

impl<T, P> IntoIterator for Punctuated<T, P> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        let mut elements = Vec::with_capacity(self.len());
        elements.extend(self.inner.into_iter().map(|pair| pair.0));
        elements.extend(self.last.map(|t| *t));

        IntoIter {
            inner: elements.into_iter(),
        }
    }
}

impl<'a, T, P> IntoIterator for &'a Punctuated<T, P> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        Punctuated::iter(self)
    }
}

impl<T, P> Default for Punctuated<T, P> {
    fn default() -> Self {
        Self::new()
    }
}

/// An iterator over owned values of type `T`.
///
/// Refer to the [module documentation] for details about punctuated sequences.
///
/// [module documentation]: self
pub struct IntoIter<T> {
    inner: vec::IntoIter<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> Clone for IntoIter<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

/// An iterator over borrowed values of type `&T`.
///
/// Refer to the [module documentation] for details about punctuated sequences.
///
/// [module documentation]: self
pub struct Iter<'a, T> {
    // The `Item = &'a T` needs to be specified to support rustc 1.31 and older.
    // On modern compilers we would be able to write just IterTrait<'a, T> where
    // Item can be inferred unambiguously from the supertrait.
    inner: Box<dyn IterTrait<'a, T, Item = &'a T> + 'a>,
}

trait IterTrait<'a, T: 'a>: DoubleEndedIterator<Item = &'a T> + ExactSizeIterator<Item = &'a T> {
    fn clone_box(&self) -> Box<dyn IterTrait<'a, T, Item = &'a T> + 'a>;
}

use std::{option, slice};
struct PrivateIter<'a, T, P> {
    inner: slice::Iter<'a, (T, P)>,
    last: option::IntoIter<&'a T>,
}

// No Clone bound on T.
impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone_box(),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, T, P> Iterator for PrivateIter<'a, T, P> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|pair| &pair.0).or_else(|| self.last.next())
    }
}

impl<T, P> DoubleEndedIterator for PrivateIter<'_, T, P> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.last.next().or_else(|| self.inner.next_back().map(|pair| &pair.0))
    }
}

impl<T, P> ExactSizeIterator for PrivateIter<'_, T, P> {
    fn len(&self) -> usize {
        self.inner.len() + self.last.len()
    }
}

// No Clone bound on T or P.
impl<T, P> Clone for PrivateIter<'_, T, P> {
    fn clone(&self) -> Self {
        PrivateIter {
            inner: self.inner.clone(),
            last: self.last.clone(),
        }
    }
}

impl<'a, T: 'a, I> IterTrait<'a, T> for I
where
    I: DoubleEndedIterator<Item = &'a T> + ExactSizeIterator<Item = &'a T> + Clone + 'a,
{
    fn clone_box(&self) -> Box<dyn IterTrait<'a, T, Item = &'a T> + 'a> {
        Box::new(self.clone())
    }
}
