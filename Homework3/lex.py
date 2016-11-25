import  ply.lex as lex
tokens = ['VARIABLE', 'CONSTANT', 'NOT', 'AND', 'OR',
          'BRACKETOPEN', 'BRACKETCLOSE',  'IMPLICATION','COMMA']
t_ignore = ' \t'
t_VARIABLE = r'[a-z]+'
t_CONSTANT = r'[A-Z][a-z]+'
t_NOT = r'~'
t_AND = r'&'
t_OR = r'\|'
t_BRACKETOPEN = r'\('
t_BRACKETCLOSE = r'\)'
t_IMPLICATION = '=>'
t_COMMA = r','

def t_error(test):
    print "error"

print lex.lex()
lex.input('DAD(xaay,yolo) & F(y)) => C(x,y) & AT(YOLO)')
while True:
    tok = lex.token()
    if not tok: break
    else:
        print tok