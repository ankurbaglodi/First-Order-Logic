import re
import ply.lex as lex
import ply.yacc as yacc
import os

from django.contrib.gis.gdal.raster import const

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


t_VARIABLE = r"[A-Z][a-z]* [(] ( [A-Za-z]*) ([,] [A-Za-z]*)*[)]"
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
    p[0] = [p[2],p[3],p[4]]

def p_pred_OR(p):
    """pred : LBRACKET pred OR pred RBRACKET"""
    p[0] = [p[2] , p[3] , p[4]]

def p_pred_IMPLICATION(p):
    """pred : LBRACKET pred IMPLICATION pred RBRACKET"""
    p[0] = [p[2] ,p[3] ,  p[4]]

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
    if len(x) == 3 and x[1] == "=>" and type(x) == list:
        x[1] = "|"
        listing1 = []
        listing1.append("~")
        listing1.append(removeImply(x[0]))
        listing2 = removeImply(x[2])
        x[0] = listing1
        x[2] = listing2
        return x
    else:
        return x

def convertToPreOrder(x):
    if type(x)==list and len(x) == 3:
        left = x[0]
        right = x[2]
        oper = x[1]
        listing  = []
        listing.append(oper)
        listing.append(convertToPreOrder(left))
        listing.append(convertToPreOrder(right))
        return listing
    elif type(x) == list and len(x) == 2:
        op = x[0]
        lhs = x[1]
        listing = []
        listing.append(op)
        listing.append(convertToPreOrder(lhs))
        return listing
    elif type(x) == str:
        return x

def moveNotInwards_orig(x):
    if type(x) == list and  x[0] == '~' :
        if len(x[1]) == 3 and type(x) == list:
            op = x[1][1]
            left = x[1][0]
            right = x[1][2]
            listing = []
            listing.append(moveNotInwards(left))
            listing.append("&" if op == '|' else "|" )
            listing.append(moveNotInwards(right))
            return listing
        elif type(x) == list and len(x[1]) == 2 :
            if x[1][0] == '~':
                listing = moveNotInwards(x[1][1])
                return listing
    elif type(x) == str:
        return x

def moveNotInwards(x):
    if type(x)== list and len(x) == 2 and x[0] == "~":
        if type(x[1]) == str:
            return x
        elif type(x[1]) == list and len(x[1]) == 2 and x[1][0] == "~":
            listing = moveNotInwards(x[1][1])
            return listing
        elif type(x[1]) == list and len(x[1]) == 3:
            listing = []
            temp = moveNotInwards(["~",x[1][0]])
            listing.append(temp)
            listing.append("&" if x[1][1] == "|" else "|")
            temp = moveNotInwards(["~",x[1][2]])
            listing.append(temp)
            # listing.append("~")
            # listing.append( moveNotInwards(x[1][0]))
            # listing.append("&" if x[1][1] == "|" else "|")
            # listing.append("~")
            # listing.append(moveNotInwards(x[1][2]))
            return listing
    elif type(x) == list and len(x) == 3 :
        x[0] = moveNotInwards(x[0])
        x[2] = moveNotInwards(x[2])
        return x
    elif type(x) == str:
        return x

def checkForDistribution_orig(x):
    """
    4 Cases to handle recursively:
     (a&b) | c
     a | (b&c)
     (a&b) | (c&d)
     a | b

     Call this from a master function
    :param x:
    :return:
    """
    if x[1] == "|":
        if 3 == len(x[0]) and  x[0][1] == '&':
            return True
        elif 3 == len(x[2]) and x[2][1] == '&':
            return True
        else:
            return False
    else:
        return False

def masterCheckForDistribution(x):
    """
    Calls checkForDistribution to check for the validity of the most atomic function
    :param x:
    :return:
    """
    retCode = False
    if len(x) == 3:
        print "Logic here"
        # for i
    else:
        return retCode


def checkForDistribution(x):
    #Check for middle element
    if list == type(x) and x[1] == "|" :
        queue = []
        queue.append(x)
        while (len(queue) != 0):
            temp = queue.pop(0)
            left = temp[0]
            right = temp[2]
            if len(left) == 3 and type(left) == list and left[1] == '&':
                return True
            if len(right) == 3 and type(right) == list and right[1] == '&':
                return True
            if len(left) != 2 and len(left) != 1 and list == type(left):
                queue.append(left)
            if len(right) != 2 and len(right) != 1 and list == type(right):
                queue.append(right)
        return False
    else:
        return False

def removeDistributionMaster(x):
    #Check if distribution can be done
    retCode = checkForDistribution(x)
    if retCode:
        x = removeDistributionChild(x)

    for i in range(0,len(x)):
        if len(x[i]) > 1:
            x[i] = removeDistributionMaster(x[i])

    retCode = checkForDistribution(x)
    if retCode:
        x = removeDistributionChild(x[i])

    return x

def removeDistributionChild(x):
    """
    Need to handel 3 cases
    1) (a&b) | (c&d)
    2) (a&b) | c
    3) a | (b&c)
    :param x:
    :return:
    """
    output = []

    #Check for case one
    if "&" == x[0][1] and "&" == x[2][1] and list == type(x[0]) and list == type(x[2]):
        #Now remove the disjunction and make it as conjuntion
        output.append(([x[0][0], "|" , x[2][0]]))
        output.append("&")
        output.append(([x[0][0], "|", x[2][2]]))
        output.append("&")
        output.append(([x[0][2], "|", x[2][0]]))
        output.append("&")
        output.append(([x[0][2], "|", x[2][2]]))
    else:
        #Handle second case
        if "&" == x[0][1] and list == type(x[0]):

            #Check if such a case is present
            # (a&b) | (c|(d&e))
            if len(x[2]) == 3 :
                retCode = checkForDistribution(x[2])
                if retCode:
                    x[2] = removeDistributionMaster(x[2])

                    #It will now be converted to (a&b) | ( (c |d) & (c|e) )
                    #Perform distribution
                    output.append(([x[0][0], "|", x[2][0]]))
                    output.append("&")
                    output.append(([x[0][0], "|", x[2][2]]))
                    output.append("&")
                    output.append(([x[0][2], "|", x[2][0]]))
                    output.append("&")
                    output.append(([x[0][2], "|", x[2][2]]))
                else:
                    #It will be in the same form as before
                    output.append(([x[0][0] , "|" , x[2] ]))
                    output.append("&")
                    output.append(([x[0][2], "|", x[2]]))
            else:
                # It will be in the same form as before
                output.append(([x[0][0], "|", x[2]]))
                output.append("&")
                output.append(([x[0][2], "|", x[2]]))

        #Handle third case
        elif "&" == x[2][1] and list == type(x[2]) :
                #Check if the following case is present
                # (a| (b&c)) | (c & d)
                if len(x[0]) == 3:
                    retCode = checkForDistribution(x[0])
                    if retCode:
                        x[0] = removeDistributionMaster(x[0])
                        #It will now convert to the same explanation as above
                        output.append(([x[0][0], "|", x[2][0]]))
                        output.append(([x[0][0], "|", x[2][2]]))
                        output.append("&")
                        output.append(([x[0][2], "|", x[2][0]]))
                        output.append(([x[0][2], "|", x[2][2]]))
                    else:
                        output.append(([x[0] , "|" , x[2][0]]))
                        output.append("&")
                        output.append(([x[0], "|" , x[2][2]]))
                else:
                    output.append(([x[0], "|", x[2][0]]))
                    output.append("&")
                    output.append(([x[0], "|", x[2][2]]))
        else:
            return x

    return output if len(output) > 0 else x

def reduceTheKB(x):
    if list == type(x):
        #Check (a | (b&c) )
        if 3 == len(x) and list == type(x) and str == type(x[0]) and list == type(x[2]):
            right = x[2]
            if 3 == len(right) and list == type(right) and str == type(right[0]) and str == type(right[2]):
                return removeDistributionChild(x)
            else:
                x[0] = reduceTheKB(x[0])
                x[2] = reduceTheKB(x[2])
                return removeDistributionChild(x)

        elif 3 == len(x) and list == type(x) and list == type(x[0]) and str == type(x[2]):
            left = x[0]
            if 3 == len(left) and list == type( left) and str == type(left[0]) and str == type(left[2]):
                return removeDistributionChild(x)
            else:
                x[0] = reduceTheKB(x[0])
                x[2] = reduceTheKB(x[2])
                return removeDistributionChild(x)

        elif 3 == len(x) and list == type(x) and list == type(x[0]) and list == type(x[2]):
            left = x[0]
            right = x[2]
            if 3 == len(left) and 3 == len(right) and \
                list == type(left) and list == type(right)  and\
                    (type(left[0]) == str or (len(left[0]) == 2 and type(left[0][1]) == str)) and\
                    (type(left[2]) == str or (len(left[2])== 2 and type(left[0][2]) == str)) and \
                    (type(right[0]) == str or (len(right[0]) == 2 and type(right[0][1]) == str)) and \
                    (type(right[2]) == str or (len(right[2]) == 2 and type(right[0][2]) == str)):
                return removeDistributionChild(x)
            else:
                x[0] = reduceTheKB(x[0])
                x[2] = reduceTheKB(x[2])
                return removeDistributionChild(x)
        else:
            return x
    else:
        return x

def removeInnerBracket(x):
    if x[1] == "&" and len(x) == 3:
        output = []
        queue = []
        for iterator in range(len(x)):
            if x[iterator] != '&' and list == type(x):
                queue.append(x[iterator])
        while (len(queue) != 0):
            temp = queue.pop(0)
            if list == type(temp) and temp[1] == '|':
                output.append(temp)
            else:
                for iterator in range(len(temp)):
                    if x[iterator] != '&' and list == type(temp):
                        queue.append(temp[iterator])
        return output
    else:
        return x


parser = yacc.yacc()
lexer = lex.lex()


# test =  parser.parse(" ((((A(x,y) | B(x,y)) & C(x,y)) | ( D(x,y)| E(x,y))) => Y(a,u))")
# test = parser.parse("((~(A(x,y) | B(y,z))) => (~(E(x,y) | D(y,z))))")
# test = parser.parse("((~A(x,y)) => B(x,y))")
# test = parser.parse("(~(~(~A(x,y))))")
# test = parser.parse("((A(x,y) => B(x,y)) => (T(x,y) => R(x,y)))")
# test = parser.parse("(~(B(x,y) & R(x,y)))")
# test = parser.parse("((~(A(x,y) & B(x,y))) | (~(Q(x,y) | R(x,y))))")
# test = parser.parse("(~((~(A(x,y) & B(x,y))) | (~(Q(x,y) | R(x,y)))))")
# test = parser.parse("(A(x,y) => (~B(r,t)))")
# test = parser.parse("((~A(x,y)) => B(r,t))")
# test = parser.parse("(  B(x,y) | ((C(x,y) & E(x,y) )  | A(x,y) ) )")
# test = parser.parse("((A(x,y) & C(x,y) ) | B(x,y)  )")
# test = parser.parse("((A(x,y) & B(x,y)) | C(x,y) )")
# test = parser.parse("(A(x,y) | ( B(x,y) & C(c,y)))")
# test = "(     ( ( Alpha(x,y)   & Beta(Elephant,x) ) & Car(yolo,boy) )    | ( Egg(x) & Fish(gang) )  )  ".replace(" ","")
# test = "(((((~A(a,y)) & B(x,y)) & C(x,y)) & D(x,y)) | (((E(a,y) & Fish(x,y)) & G(x,y)) & H(x,y)))"
# test = "(A(x) => H(x))"
# test = "A(x,y)"
# test = "(((Razer(A,B,xx,x) => Blade(a))  =>  Temp(x)   ) => (Cat(x,y,z,a)))   ".replace(" ","")
# test = "(((Razer(A,B,xx,x) => Blade(a)) => Temp(x)) => Cat(x,y,z))".replace(" ","")
# test = "((( A(x) | (C(x) & D(x))) => (E(x,y) => D(g))) => ((~X(y)) => Apple(Dog)))".replace(" ","")
# test = "((A(x) | (C(x) & D(x))) | (X(y) | Apple(Dog)))" .replace(" ","")
test = "(((A(x) & (E(x) | X(x))) | D(x) ) | (B(x) & C(x)))"
print test


test = parser.parse(test)
print test



test = removeImply(test)
print test
print "--------------------"
# print test[0]
# print test[1]
# print test[2]
print "-------------"
test1 = moveNotInwards(test)
print test1
# print test1[0]
# print test1[1]
# print test1[2]
print checkForDistribution(test1)
# print "------------------"
test2 = reduceTheKB(test1)
print "123456"
print test2
# test2 =  removeDistributionMaster(test1)
# print len(test2)
# print test2
test3 = removeInnerBracket(test2)
print len(test3)
print test3[0]
print test3[1]


# print test2[0][1]
# print re.findall(r"(\W?\w+)\(",test2[0][1])
print (re.findall(r'\(([\w+]|[\w+,\w+]*)\)',test2[0][1])).split(',')

# testing1 = "Ankur(xx,yy)"
# testing2 = "Ankur(y,ZZ)"
# listOfVariables1 = splitThePredicate(testing1)
# listOfVariables2 = splitThePredicate(testing2)
# print listOfVariables1, listOfVariables2
# print unify(listOfVariables1[1], listOfVariables2[1])
#
# print test2[0][1].index("(")
# print test2[0][1].index(")")
print test2[0][1][test2[0][1].index("(")+1 : test2[0][1].index(")")].split(",")

# test = moveNotInwards(test)
# test1 =  convertToPreOrder(test)

# assert convert_to_cnf(ply_parse(" (~(B|C))")) == ['~', 'B', '&', '~', 'C']
# assert convert_to_cnf(ply_parse("  (~ (~ (Roger(x,y,z) ) ) )  ")) == "Roger(x,y,z)"
# assert convert_to_cnf(ply_parse(" (~ ( B & C ) ) ")) == ['~', 'B', '|', '~', 'C']
# print convert_to_cnf(ply_parse(" ( ~( (~(B & C) ) |  (~(E | F)) ) )  "))
# print ply_parse(" ( ~( (~(B & C) ) |  (~(E | F)) ) )  ")
# NEGATION ~ (  ~( B & C ) | ~ (E | F) )



# parseList =  parser.parse("((A(x,y) => (Z(a,t) => (( ~ E(x,t)) => (~ H(x,i))))) => (C(x,y) => D(x,y)))".replace(" ",""),lexer)
# print parseList
# if parseList[1] == "=>":
#     parseList[0] = removeImply(parseList[0])
#     parseList[1] = "|"
#     if len(parseList[2]) == 3 and parseList[2][1] == "=>":
#         removeImply(parseList[2])
# print parseList

























#
# readFile()
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
# assert parser
