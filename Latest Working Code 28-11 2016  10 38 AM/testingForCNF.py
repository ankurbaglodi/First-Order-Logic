import ply.lex as lex
import ply.yacc as yacc
import os

readFileList = []
def readFile():
    """
    Just read the file and stores in the variable readFile
    :return: nothing
    """
    try:
        if os.path.exists("input.txt"):
            f = open('input.txt', 'r')
            for each_line in f:
                readFileList.append(each_line.strip())
    finally:
        f.close()
        return  0

tokens = ('VARIABLE',  'NOT', 'AND', 'OR',
          'LBRACKET', 'RBRACKET', 'IMPLICATION', 'COMMA')

# t_VARIABLE = r"[A-Z][(]?[a-z]*([,][a-z])*[)]?"
t_VARIABLE = r"[A-Z][a-z]* [(]? ( [A-Za-z]*) ([,] [A-Za-z]*)*[)]?"
# t_CONSTANT = r'[A-Z][A-Za-z]*'
t_NOT = r'~'
t_AND = r'&'
t_OR = r'\|'
t_LBRACKET = r'\('
t_RBRACKET = r'\)'
t_IMPLICATION = r'=>'
t_COMMA = r','
t_ignore = " \t"

precedence = (
    ('left', 'LBRACKET'),
    ('left', 'RBRACKET'),
    ('left', 'NOT'),
    ('left', 'AND'),
    ('left', 'OR'),
    ('right', 'IMPLICATION')
)

def p_pred_NOT(p):
    """pred : LBRACKET NOT pred RBRACKET"""
    p[0] = [p[2],p[3]]

def p_pred_AND(p):
    """pred : LBRACKET pred AND pred RBRACKET"""
    p[0] = [p[3],p[2],p[4]]

def p_pred_OR(p):
    """pred : LBRACKET pred OR pred RBRACKET"""
    p[0] = [p[3] ,p[2] ,  p[4]]

def p_pred_IMPLICATION(p):
    """pred : LBRACKET pred IMPLICATION pred RBRACKET"""
    p[0] = [p[3] ,p[2] ,  p[4]]

def p_pred_terminal(p):
    """pred : VARIABLE"""
    p[0] = p[1]

def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


def p_error(p):
    if p:
        print("Syntax error at '%s'" % p.value)
    else:
        print("Syntax error at EOF")

def removeImply(x):
    if len(x) == 3 and x[1] == "=>":
        x[1] = '|'
        x[0] = removeImply(x[0])
        return x[2]
    else:
        return ['~',x]




# lex.lex()
parser =  yacc.yacc()
lexer = lex.lex()

parseList =  parser.parse("((D(x,y) & F(y)) => C(x,y))")
print parseList
if parseList[1] == "=>":
    parseList[0] = removeImply(parseList[0])
    parseList[1] = "|"
print parseList

readFile()
# a = "(~(~(~(~A(               x                  ,         dsbgkbkdfgb          )))))"
# a = a.replace(" ","")
# assert parser.parse(a , lexer) == ['~', ['~', ['~', ['~', 'A(x,dsbgkbkdfgb)']]]]
# assert parser.parse("((~A(x,y)) & B(usdibfvskj,oidfhndfjnh))") == [['~', 'A(x,y)'], '&', 'B(usdibfvskj,oidfhndfjnh)']
# assert parser.parse("((B(x,y) & C(x,y)) => A(x))",lexer) == [['B(x,y)', '&', 'C(x,y)'], '=>', 'A(x)']
# assert parser.parse("B(John,Alice)") == "B(John,Alice)"
# assert parser.parse("((D(x,y) & F(y)) => C(x,y))" , lexer) == [['D(x,y)', '&', 'F(y)'], '=>', 'C(x,y)']
# assert parser.parse("(F(x) => G(x))") == ['F(x)', '=>', 'G(x)']
# assert parser.parse("R(Alice)") == 'R(Alice)'
# assert parser.parse("Mother(Liz,Charley)") == "Mother(Liz,Charley)"
# assert parser.parse("((~Mother(x,y)) | Parent(x,y))") == [['~', 'Mother(x,y)'], '|', 'Parent(x,y)']
# assert parser.parse("((~(Parent(x,y) & Ancestor(y,z))) | Ancestor(x,z))") == [['~', ['Parent(x,y)', '&', 'Ancestor(y,z)']], '|', 'Ancestor(x,z)']
# assert parser.parse("(~(~(~(~A(x)))))" , lexer) == ['~', ['~', ['~', ['~', 'A(x)']]]]

# print parser.parse(a , lexer)
print parser.parse("((~A(x,y)) & B(usdibfvskj,oidfhndfjnh))")
print parser.parse("((B(x,y) & C(x,y)) => A(x))",lexer)
print parser.parse("B(John,Alice)")
print parser.parse("((D(x,y) & F(y)) => C(x,y))" , lexer)
print parser.parse("(F(x) => G(x))")
print parser.parse("R(Alice)")
print parser.parse("Mother(Liz,Charley)")
print parser.parse("((~Mother(x,y)) | Parent(x,y))")
print parser.parse("((~(Parent(x,y) & Ancestor(y,z))) | Ancestor(x,z))")
print parser.parse("(~(~(~(~A(x)))))" , lexer)
