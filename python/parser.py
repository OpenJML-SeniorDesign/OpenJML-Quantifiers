from dataclasses import dataclass
from enum import Enum, auto
import json
from typing import List, NamedTuple, TypeVar
from typing_extensions import Literal

T = TypeVar("T")


class Kind(Enum):
    NONE = auto()
    NUMBER = auto()
    SYMBOL = auto()
    OPERATOR = auto()


class Token(NamedTuple):
    kind: Kind
    value: str

    def __str__(self):
        return self.value

    def __repr__(self):
        return f"Token(kind={self.kind}, value={self.value!r})"


class Operator(Token):
    kind: Literal[Kind.OPERATOR]
    value: str


@dataclass
class AST:
    token: Token
    children: List["AST"]

    def to_json(self):
        return {
            "value": self.token.value,
            "children": list(map(AST.tojson, self.children)),
        }


def lex(jml: str):
    """
    Lex a JML Annotation into individual tokens

    :param jml: JML Annotation
    :returns: a generator that produces a single token at a time
    """
    chars = list(jml)
    while chars:
        char = chars.pop(0)
        if char.isspace():
            continue

        token = ""
        kind = Kind.NONE
        if char.isdigit():
            while char and char.isdigit():
                token += char
                char = chars.pop(0) if chars else ""
            chars.insert(0, char)
            kind = Kind.NUMBER
        elif char.isalpha() or char == "\\":
            while char and (char.isalnum() or char in "\\_."):
                token += char
                char = chars.pop(0) if chars else ""
            chars.insert(0, char)
            kind = Kind.SYMBOL
        else:
            if chars and char + chars[0] in set(("==", "<=", ">=", "&&", "||")):
                token = char + chars.pop(0)
            else:
                token = char
            kind = Kind.OPERATOR

        yield Token(kind=kind, value=token)


def precedene(op: Operator):
    v = op.value
    if v in set(("&&", "||")):
        return 0
    if v in set(("==", "<=", ">=", ">", "<", "!")):
        return 1
    if v in set(("+", "-")):
        return 2
    if v in set(("*", "/", "%")):
        return 3
    if v in set(("(", ")")):
        return -1

    error(f"unknown operator {v}")


def operator_to_smt(op: Operator):
    v = op.value
    if v == "&&":
        return "and"
    if v == "||":
        return "or"
    if v == "/":
        return "div"
    if v == "%":
        return "mod"
    if v == "!":
        return "not"
    return v


def error(msg):
    print(f"[ERR] {msg}")
    exit(1)


def expected(expected, found: Token):
    error(f"expected {expected!r} but found {found!r}")


def peek(tokens: List[Token]):
    return tokens[0] if tokens else Token(Kind.NONE, "")


def required(tokens: List[Token], target):
    token = peek(tokens)
    if token != target:
        expected(target.value, token)
    return tokens.pop(0)


def parse_expression(tokens: List[Token], start: Operator = None):
    values: List[AST] = []
    ops: List[Operator] = [start] if start else []

    token = peek(tokens)
    while tokens and token != Token(Kind.OPERATOR, ";"):
        if token == Token(Kind.OPERATOR, "("):
            ops.append(token)
        elif token.kind == Kind.NUMBER or token.kind == Kind.SYMBOL:
            values.append(AST(token, []))
        elif token == Token(Kind.OPERATOR, ")"):
            while ops and ops[-1] != Token(Kind.OPERATOR, "("):
                v1 = values.pop()
                v2 = values.pop()
                op = ops.pop()

                values.append(AST(op, [v2, v1]))
            ops.pop()
        else:
            while ops and precedene(ops[-1]) >= precedene(token):
                v1 = values.pop()
                v2 = values.pop()
                op = ops.pop()

                values.append(AST(op, [v2, v1]))
            ops.append(token)

        tokens.pop(0)
        token = peek(tokens)
    tokens.pop(0)

    while ops:
        v1 = values.pop()
        v2 = values.pop()
        op = ops.pop()

        values.append(AST(op, [v2, v1]))

    if len(values) != 1:
        error("Too many values")
    return values.pop()


def parse(tokens: List[Token]):
    required(tokens, Token(Kind.OPERATOR, "("))

    token = peek(tokens)
    if token.kind != Kind.SYMBOL:
        expected("symbol", token)

    if token.value not in ("\\sum", "\\product"):
        expected("symbol '\\sum' or '\\product'", token)
    tokens.pop(0)

    token = peek(tokens)
    if token.kind != Kind.SYMBOL:
        expected("symbol", token)

    if token.value != "int":
        expected("symbol 'int'", token)
    tokens.pop(0)

    token = peek(tokens)
    if token.kind != Kind.SYMBOL:
        expected("symbol", token)

    quant_var = token.value
    tokens.pop(0)

    required(tokens, Token(Kind.OPERATOR, ";"))

    range_pred = parse_expression(tokens)
    body_pred = parse_expression(tokens, Token(Kind.OPERATOR, "("))

    return quant_var, range_pred, body_pred


def translate(ast: AST):
    if ast.token.kind == Kind.NUMBER or ast.token.kind == Kind.SYMBOL:
        return ast.token.value

    return f"({operator_to_smt(ast.token)} {translate(ast.children[0])} {translate(ast.children[1])})"


# s = r"(\sum T x; 0 <= x && x < arr.length; arr[x])"
s = r"(\sum int x; 0 <= x && x < 5; x + 4);"
toks = list(lex(s))

print(*toks)

_, R, B = parse(toks)

print(
    f"""
(define-fun-rec sum
    ((lo Int) (hi Int) (aa array)) Int
    (ite (< hi lo)
        0
        (+
            (sum lo (- hi 1) aa)
            (ite {translate(R)}
                {translate(B)}
                0
            )
        )
    )
)
"""
)
