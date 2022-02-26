# Simple JML Expression parser and SMT Translator
# Handles most binary operators and generalized quantifiers

import argparse
from dataclasses import dataclass
from enum import Enum, auto
import json
import sys
from typing import Any, Callable, List, Optional, Tuple, TypeVar

number = TypeVar("number", int, float)


class Kind(Enum):
    NONE = auto()
    NUMBER = auto()
    SYMBOL = auto()
    OPERATOR = auto()


@dataclass(frozen=True)
class Token:
    kind: Kind
    value: str

    def __str__(self):
        return self.value

    def __repr__(self):
        return f"Token(kind={self.kind}, value={self.value!r})"


def Operator(value: str):
    return Token(kind=Kind.OPERATOR, value=value)


@dataclass
class AST:
    token: Token
    children: Optional[Tuple["AST", "AST"]]
    data: Optional[Any] = None  # extra value for quantifiers

    def to_json(self):
        return {
            "value": self.token.value,
            "children": list(map(AST.to_json, self.children or [])),
        }

    def pretty(self):
        return json.dumps(self.to_json(), indent=4)

    def flat(self) -> str:
        """flatten AST"""
        if not self.children:
            return self.token.value
        if is_quantifier(self.token):
            return f"({self.token.value} {self.data}; {self.children[0].flat()}; {self.children[1].flat()})"
        return f"{self.children[0].flat()} {self.token.value} {self.children[1].flat()}"

    def depth(self):
        if not self.children or is_quantifier(self.token):
            return 1 if self.token.value != "\\num_of" else 2
        return max(child.depth() for child in self.children) + 1


def error(msg):
    print(f"[ERR] {msg}", file=sys.stderr)
    exit(1)


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
            if chars and char + chars[0] in set(("==", "<=", ">=", "&&", "||", "!=")):
                token = char + chars.pop(0)
            else:
                token = char
            kind = Kind.OPERATOR

        yield Token(kind=kind, value=token)


def precedence(op: Token):
    # https://docs.oracle.com/javase/tutorial/java/nutsandbolts/operators.html
    assert op.kind == Kind.OPERATOR, f"expected operator but found token {op!r}"
    v = op.value
    if v == "(" or v == ")":
        return 0
    if v == "||":
        return 1
    if v == "&&":
        return 2
    if v == "==" or v == "!=":
        return 3
    if v in set(("<", ">", "<=", ">=")):
        return 4
    if v == "+" or v == "-":
        return 5
    if v in set(("*", "/", "%")):
        return 6
    if v == "!":
        return 7

    error(f"unknown operator {v!r}")


def expected(expected, found: Token):
    """throw expected token error"""
    error(f"expected {expected!r} but found {found!r}")


def peek(tokens: List[Token]):
    """safe peek"""
    return tokens[0] if tokens else Token(Kind.NONE, "")


def pop(tokens: List[Token]):
    """safe pop"""
    return tokens.pop(0) if tokens else Token(Kind.NONE, "")


def is_quantifier(token: Token):
    """is the token a JML generalized quantifier"""
    return token.kind == Kind.SYMBOL and (
        token.value in set(("\\sum", "\\product", "\\num_of"))
    )


def apply_operator(values: List[AST], ops: List[Token]):
    v1 = values.pop()
    v2 = values.pop()
    op = ops.pop()

    values.append(AST(op, (v2, v1)))


def parse_quantifier(tokens: List[Token]):
    """
    Parse a JML quantifier expression in the form:
    \quantifier T x; R(x); B(x))
    Note the missing leading '(' as that is eaten by :func: `parse_expression`
    """
    token = pop(tokens)
    if not is_quantifier(token):
        expected("quantifier symbol", token)

    quantifier = token
    token = pop(tokens)
    if token.kind != Kind.SYMBOL:
        expected("symbol", token)

    if token.value != "int":
        expected("symbol 'int'", token)

    token = pop(tokens)
    if token.kind != Kind.SYMBOL:
        expected("symbol", token)
    quant_var = token.value

    token = pop(tokens)
    if token != Operator(";"):
        expected(";", token)

    range_pred = parse_expression(tokens)
    body_pred = parse_expression(tokens, ghost_start=True)

    return AST(quantifier, (range_pred, body_pred), quant_var)


def parse_expression(tokens: List[Token], ghost_start: bool = False):
    """
    Parse a JML annotation and construct an AST.

    :param tokens: tokenized statement from :func: `lex`
    :param ghost_start: a trick to parse the body of a quantifier than ends with ')'
    :returns: an AST of the token stream
    """
    values: List[AST] = []
    ops: List[Token] = []

    token = pop(tokens)
    while tokens and token != Operator(";"):
        if token == Operator("("):
            after = peek(tokens)
            if is_quantifier(after):
                values.append(parse_quantifier(tokens))
            else:
                ops.append(token)
        elif token == Operator(")"):
            while ops and ops[-1] != Operator("("):
                apply_operator(values, ops)
            if not ops and ghost_start:
                return values[0]
            ops.pop()
        elif token.kind == Kind.NUMBER or token.kind == Kind.SYMBOL:
            values.append(AST(token, None))
        else:
            while ops and precedence(ops[-1]) >= precedence(token):
                apply_operator(values, ops)
            ops.append(token)

        token = pop(tokens)

    while ops:
        apply_operator(values, ops)

    if len(values) != 1:
        error(f"Expected value stack to have 1 value found {len(values)}")
    return values.pop()


def get_value_from_ast(
    ast: AST, compare: Callable[[number, number], number], NULL: number
):
    """gets a value from the AST tree according to the compare function"""
    if ast.children:
        left = get_value_from_ast(ast.children[0], compare, NULL)
        right = get_value_from_ast(ast.children[1], compare, NULL)
        return compare(left, right)

    if ast.token.kind == Kind.NUMBER:
        return int(ast.token.value)
    return NULL


class Translator:
    def __init__(self):
        self.header = "; computer generated"
        self.num = 0

    def _define_quantifier(
        self,
        name: str,
        operator: str,
        quant_var: str,
        range_func: str,
        body_func: str,
        base_case: int,
    ):
        self.num += 1
        self.header += f"""
(define-fun-rec {name}{self.num}
    ((lo Int) ({quant_var} Int)) Int
    (ite (< {quant_var} lo)
        {base_case}
        ({operator}
            ({name}{self.num} lo (- {quant_var} 1))
            (ite {range_func}
                {body_func}
                {base_case}
            )
        )
    )
)
"""

    def _translate_quantifier(self, ast: AST):
        if not ast.children or not ast.data:
            assert False, f"invalid quantifier node {ast}"

        name = ast.token.value[1:]
        range_func = self._translate(ast.children[0])
        body_func = self._translate(ast.children[1])

        if name == "num_of":
            range_func = f"(and {range_func} {body_func})"
            body_func = "1"

        self._define_quantifier(
            name=name,
            operator="*" if name == "product" else "+",
            quant_var=ast.data,
            range_func=range_func,
            body_func=body_func,
            base_case=1 if name == "product" else 0,
        )

        minimum = get_value_from_ast(ast.children[0], min, float("inf"))
        maximum = get_value_from_ast(ast.children[0], max, float("-inf"))
        return f"({name}{self.num} {minimum} {maximum})"

    def _operator_to_smt(self, op: Token) -> str:
        assert op.kind == Kind.OPERATOR, f"expected operator but found {op!r}"
        maping = {
            "&&": "and",
            "||": "or",
            "/": "div",
            "%": "mod",
            "!": "not",
            "==": "=",
        }
        return maping.get(op.value, op.value)

    def _translate(self, ast: AST):
        if not ast.children:
            return ast.token
        if is_quantifier(ast.token):
            return self._translate_quantifier(ast)

        return f"({self._operator_to_smt(ast.token)} {self._translate(ast.children[0])} {self._translate(ast.children[1])})"

    def translate(self, ast: AST):
        body = self._translate(ast)
        return f"{self.header}\n(assert (not {body}))\n(check-sat)"


class TranslatorWithSteps:
    """Show translation steps"""

    def __init__(self):
        self.num = 0  # denotes unique number for each quantifier
        self.quants = ""  # used for declaration translations
        self.quants_handled = set()

    def _define_quantifier(
        self,
        name: str,
        operator: str,
        quant_var: str,
        range_func: List[str],
        body_func: List[str],
        base_case: int,
    ):
        """Create quantifier declaration translations for range and body expressions"""
        self.num += 1
        if f"{name}{self.num}" in self.quants_handled:
            return
        self.quants_handled.add(f"{name}{self.num}")

        self.quants += f"\nDECLARATION TRANSLATION OF {name.upper()}"
        for rf in range_func:
            self.quants += f"""
    (define-fun-rec {name}{self.num}
        ((lo Int) ({quant_var} Int)) Int
        (ite (< {quant_var} lo)
            {base_case}
            ({operator}
                ({name}{self.num} lo (- {quant_var} 1))
                (ite {rf}
                    {body_func[0]}
                    {base_case}
                )
            )
        )
    )
    """
        for bf in body_func[1:]:
            self.quants += f"""
    (define-fun-rec {name}{self.num}
        ((lo Int) ({quant_var} Int)) Int
        (ite (< {quant_var} lo)
            {base_case}
            ({operator}
                ({name}{self.num} lo (- {quant_var} 1))
                (ite {range_func[-1]}
                    {bf}
                    {base_case}
                )
            )
        )
    )
    """

    def _translate_quantifier(self, ast: AST):
        if not ast.children or not ast.data:
            assert False, f"invalid quantifier node {ast}"

        name = ast.token.value[1:]
        base = self.num
        range_func = self._translate_steps(ast.children[0], base)
        body_func = self._translate_steps(ast.children[1], base)

        self._define_quantifier(
            name=name,
            operator="*" if name == "product" else "+",
            quant_var=ast.data,
            range_func=range_func,
            body_func=body_func,
            base_case=1 if name == "product" else 0,
        )

        minimum = get_value_from_ast(ast.children[0], min, float("inf"))
        maximum = get_value_from_ast(ast.children[0], max, float("-inf"))
        return f"({name}{self.num} {minimum} {maximum})"

    def _operator_to_smt(self, op: Token) -> str:
        assert op.kind == Kind.OPERATOR, f"expected operator but found {op!r}"
        maping = {
            "&&": "and",
            "||": "or",
            "/": "div",
            "%": "mod",
            "!": "not",
            "==": "=",
        }
        return maping.get(op.value, op.value)

    def _translate(self, ast: AST, depth: int, max_depth: int):
        if depth > max_depth:
            return ""
        if depth == max_depth:
            return f"[[{ast.flat()}]]"

        if not ast.children:
            return f"{ast.token}"
        if is_quantifier(ast.token):
            if ast.token.value[1:] == "num_of":  # convert num_of to a sum
                return self._translate(
                    AST(
                        Token(Kind.SYMBOL, "\\sum"),
                        (
                            AST(Operator("&&"), ast.children),
                            AST(Token(Kind.NUMBER, "1"), None),
                        ),
                        data=ast.data,
                    ),
                    depth,
                    max_depth - 1,
                )
            return self._translate_quantifier(ast)

        return f"({self._operator_to_smt(ast.token)} {self._translate(ast.children[0], depth+1, max_depth)} {self._translate(ast.children[1], depth+1, max_depth)})"

    def _translate_steps(self, ast: AST, start_num: int = 0) -> List[str]:
        out = []
        for i in range(ast.depth() + 1):
            self.num = start_num
            out.append(self._translate(ast, 0, i))
        return out

    def translate(self, ast: AST) -> str:
        body = "\n".join(self._translate_steps(ast))
        return f"""{self.quants}\n\nUSAGE TRANSLATIONS\n{body}"""


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Tool to build SMT Translations.",
        epilog="Try the input: (\\sum int x; 0 <= x && x < 5; x) == 1 + 2 + 3 + 4;",
    )
    parser.add_argument("-f", "--file", help="input JML file, default stdin")
    parser.add_argument("-o", "--out", help="output SMT file, default stdout")
    parser.add_argument(
        "-s", "--steps", action="store_true", help="output translation steps"
    )

    args = parser.parse_args()

    if args.file:
        with open(args.file, "r") as f:
            jml = f.read()
    else:
        jml = input("Input: ")

    tokens = list(lex(jml))
    expression = parse_expression(tokens)

    smt = (TranslatorWithSteps() if args.steps else Translator()).translate(expression)
    if args.out:
        with open(args.out, "w") as f:
            f.write(smt)
    else:
        print(smt)
