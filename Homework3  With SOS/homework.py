import os, sys , ply.lex as lex
import lex
readFileList = []

# def lexer():
#     tokens = ['VARIABLE', 'CONSTANT', 'NOT', 'AND', 'OR',
#               'BRACKETOPEN', 'BRACKETCLOSE', 'FUNCTION' , 'IMPLICATION' ]
#     t_ignore = ' \t'
#     t_VARIABLE = r'[a-z]*'
#     t_CONSTANT = r'[A_Z]*'
#     t_NOT = r'~'
#     t_AND = r'&'
#     t_OR = r'|'
#     t_BRACKETOPEN = r'\('
#     t_BRACKETCLOSE = r'\)'
#     t_FUNCATION = r'[A-Z]*'
#     t_IMPLICATION = '=>'
#
# def t_error(test):
#     print "error"

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

if __name__ == "__main__":
    #read the file and store in a variable
    readFile()
    # print readFileList
    lex.lex()
    lex.input('DAD(xaay,yolo) & F(y)) => C(x,y) & AT(YOLO)')
    while True:
        tok = lex.token()
        if not tok: break
        else:
            print tok