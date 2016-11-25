import ply.lex as lex
import ply.yacc as yacc
import os,re
from collections import defaultdict
import copy

#Global variables Used by the program
#===============================================================#
readFileList = [] #Used to store the input file
counter = 1 #Used to standarize variables
#===============================================================#

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

#Parser starts here
#===================================================================#

tokens = ('VARIABLE',  'NOT', 'AND', 'OR',
          'LBRACKET', 'RBRACKET', 'IMPLICATION', 'COMMA')


t_VARIABLE = r"[A-Za-z0-9]* [(] ( [A-Za-z0-9]*) ([,] [A-Za-z0-9]*)*[)]"
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
#==========================================================================#
#Parser ends here

#Functions required to convert the statements to CNF starts here
#==========================================================================#
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
            if len(left) != 2 and len(left) != 1:
                queue.append(left)
            if len(right) != 2 and len(right) != 1:
                queue.append(right)
        return False
    else:
        return False


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
                    x[2] = (x[2])

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
                        x[0] = (x[0])
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
    if x[1] == "&" and len(x) > 3:
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
                    if list ==  type (temp) and x[iterator] != '&' :
                        queue.append(temp[iterator])
        return output
    else:
        return x
#==========================================================================#
#Functions requred to convert to CNF ends here

#Functions concentrated on working on KB and the algorithm
#==========================================================================#

#Function to create table indexing
def buildTableIndexing(KBList, tableIndexPositive, tableIndexNegative):
    for iterator in range(0,len(KBList)):
        queue = []
        queue.append(KBList[iterator])
        while(len(queue) != 0):
            temperory = queue.pop(0)
            if str == type(temperory):
                temperory = re.findall(r"(\W?\w+)\(", temperory)[0]
                tableIndexPositive[temperory].append(iterator)
            elif list == type(temperory) and 2 == len(temperory) and temperory[0] == '~':
                temperory = re.findall(r"(\W?\w+)\(", temperory[1])[0]
                tableIndexNegative[temperory].append(iterator)
            else:
                for subiterator in range(0,len(temperory)):
                    if "|" != temperory[subiterator]:
                        queue.append(temperory[subiterator])
    return tableIndexPositive,tableIndexNegative

def buildIndexRehash(tableIndexPositive, tableIndexNegative,statement,indexInKB):
    queue = []
    queue.append(statement)
    while (len(queue) != 0):
        temperory = queue.pop(0)
        if str == type(temperory):
            temperory = re.findall(r"(\W?\w+)\(", temperory)[0]
            tableIndexPositive[temperory].append(indexInKB)
        elif list == type(temperory) and 2 == len(temperory) and temperory[0] == '~':
            temperory = re.findall(r"(\W?\w+)\(", temperory[1])[0]
            tableIndexNegative[temperory].append(indexInKB)
        else:
            for subiterator in range(0, len(temperory)):
                if "|" != temperory[subiterator]:
                    queue.append(temperory[subiterator])


    return tableIndexPositive, tableIndexNegative


def removeAllInnerBracketForDisjunction(x):
    output = []
    queue = []
    queue.append(x)
    while (len(queue) != 0):
        temp = queue.pop(0)
        if len(temp) >= 3 and list == type(temp):
            if ((str == type(temp[0])) or (list == type(temp[0]) and 2 == len(temp[0]))):
                output.append(temp[0])
                output.append("|")
            else:
                queue.append(temp[0])
            if (str == type(temp[2]) or (list == type(temp[2]) and 2 == len(temp[2]))):
                output.append(temp[2])
                output.append("|")
            else:
                queue.append(temp[2])
    if len(output) > 0:
        if output[-1] == "|":
            return output[:len(output)-1]
        else:
            return output
    else:
        return x

#Function to standarize variables in KB
def standarizeKB(x):
    global counter
    if list == type(x):
        for iterator in range(0,len(x)):
            temp = x[iterator]
            if temp != '|' and temp != '&' and temp != '~':
                #Need to handle two cases
                #1) with ~ it comes in as a list
                #2) with the regular predicate is it alright
                if list == type(temp) and 2 == len(temp):
                    atomizeVariables = temp[1][temp[1].index("(")+1:temp[1].index(")")].split(",")
                    predicate = temp[1][:temp[1].index("(")]
                    atomicVariableString = ""
                    for subiterator in range(0,len(atomizeVariables)):
                        atomizeVariables[subiterator] = atomizeVariables[subiterator] if\
                                                        atomizeVariables[subiterator][0].isupper()  \
                                                        else atomizeVariables[subiterator] + str(counter)
                        atomicVariableString += atomizeVariables[subiterator] + ","
                    x[iterator][1] = predicate + "(" + atomicVariableString[:len(atomicVariableString) - 1] + ")"
                elif str == type(temp):
                    atomicVariableString = ""
                    atomizeVariables = temp[temp.index("(") + 1:temp.index(")")].split(",")
                    predicate = temp[:temp.index("(")]
                    for subiterator in range(0,len(atomizeVariables)):
                        atomizeVariables[subiterator] = atomizeVariables[subiterator] if\
                                                        atomizeVariables[subiterator][0].isupper()  \
                                                        else atomizeVariables[subiterator] + str(counter)
                        atomicVariableString += atomizeVariables[subiterator] + ","
                    x[iterator] = predicate + "(" + atomicVariableString[:len(atomicVariableString)-1] + ")"
    elif str == type(x):
        temp = x
        atomicVariableString = ""
        atomizeVariables = temp[temp.index("(") + 1:temp.index(")")].split(",")
        predicate = temp[:temp.index("(")]
        for subiterator in range(0, len(atomizeVariables)):
            atomizeVariables[subiterator] = atomizeVariables[subiterator] if \
                atomizeVariables[subiterator][0].isupper() \
                else atomizeVariables[subiterator] + str(counter)
            atomicVariableString += atomizeVariables[subiterator] + ","
        x = predicate + "(" + atomicVariableString[:len(atomicVariableString) - 1] + ")"

    counter += 1
    return x

def splitThePredicate(temp):
    if temp != "|" and temp != "&":
        if list == type(temp) and 2 == len(temp):
            atomizeVariables = temp[1][temp[1].index("(") + 1:temp[1].index(")")].split(",")
            predicate = temp[1][:temp[1].index("(")]
            return predicate,atomizeVariables
        elif str == type(temp):
            atomizeVariables = temp[temp.index("(") + 1:temp.index(")")].split(",")
            predicate = temp[:temp.index("(")]
            return predicate, atomizeVariables
        else:
            return temp
    else:
        return temp

def unify(variablesFromExp1,variablesFromExp2,tempDict):
    if len(variablesFromExp1) != len(variablesFromExp2):
        return False,tempDict
    else:
        for iterator in range(0,len(variablesFromExp2)):
            tempFirst   = variablesFromExp1[iterator]
            tempSecond  = variablesFromExp2[iterator]
            if tempFirst[0].isupper() and str == type(tempFirst) and\
                    tempSecond[0].isupper() and str == type(tempSecond):
                if tempFirst == tempSecond:
                    continue
                else:
                    return False,tempDict
            elif tempFirst[0].isupper() and str == type(tempFirst) and\
                    tempSecond[0].islower() and str == type(tempSecond):
                if tempSecond not in tempDict:
                    tempDict[tempSecond] = tempFirst
            elif tempFirst[0].islower() and str == type(tempFirst) and \
                    tempSecond[0].isupper() and str == type(tempSecond):
                if tempFirst not in tempDict:
                    tempDict[tempFirst] = tempSecond
            else:
                tempDict[tempFirst] = tempSecond
        return True,tempDict


def newUnify(variable1,variable2,tempDict):
    if tempDict == False:
        return False
    elif variable1 == variable2:
        return tempDict
    elif type(variable1) == str and variable1[0].islower():
        tempDict = unifyChilding(variable1, variable2, tempDict)
        return tempDict
    elif type(variable2) == str and variable2[0].islower():
        tempDict = unifyChilding(variable2, variable1, tempDict)
        return tempDict
    elif type(variable1) == type(variable2) and type(variable2) == list:
        tempDict = newUnify(variable1[1:], variable2[1:], newUnify(variable1[0], variable2[0], tempDict))
        return tempDict
    else:
        return False

def unifyChilding(variable1,variable2,tempDict):
    if variable1 in tempDict:
        return newUnify(tempDict[variable1],variable2,tempDict)
    elif variable2 in tempDict:
        return newUnify(variable1,tempDict[variable2],tempDict)
    else:
        if variable1[0].islower()==True:
            tempDict[variable1] = variable2
            return tempDict
        elif variable2[0].islower() == True:
            tempDict[variable2] = variable1
            return tempDict



def refuteNewClause(temp):
    if str == type(temp):
        output = []
        output.append('~')
        output.append(temp)
    elif list == type(temp) and 2 == len(temp) and '~' == temp[0] and str == type(temp[1]):
        output = temp[1]
    else:
        print "Something went wrong in the query, check the queries given in the question."
    return output


def replaceVariableInAPredicate(x,dictionary):
    if str == type(x) or (list == type(x) and 2 == len(x)):
        return  replaceVariableInAPredicateChild(x,dictionary)
    elif list == type(x) and 3 <= len(x):
        newPred = []
        for iterator in x:
            if iterator != '~' and iterator != '&' and iterator != '|':
                newPred.append(replaceVariableInAPredicateChild(iterator,dictionary))
                newPred.append("|")
        return newPred[:-1]


def replaceVariableInAPredicateChild(x,dictinonary):
    newVariables = []
    isNegated = False
    if 2 == len(x) and list == type(x) and '~' == x[0] and str == type(x[1]):
        temp = x[1]
        isNegated = True
    elif str == type(x):
        temp = x
    else:
        temp = False
    splitPredicateForCreatingNewOne = splitThePredicate(temp)
    #Either variable : variable or variable : constant
    #Thumb rule is to put the key in all the variablles
    for variable in splitPredicateForCreatingNewOne[1]:
        if variable != '~' and variable!= '&' and variable != '|':
            if variable[0].isupper() == True:
                newVariables.append(variable)
            elif variable[0].islower() == True:
                if variable in dictinonary:
                    newVariables.append(dictinonary[variable])
                elif variable in dictinonary.values():
                    newVariables.append(variable)
                else:
                    newVariables.append(variable)

    #Now construct new string for the predicate
    if isNegated == True:
        newPredicate = []
        newPredicate.append('~')
        tempStrForNewVariables = ""
        for iterator in newVariables:
            tempStrForNewVariables += iterator+","
        newPredicate.append(splitPredicateForCreatingNewOne[0] + "(" + tempStrForNewVariables[:len(tempStrForNewVariables)-1] + ")")
    else:
        tempStrForNewVariables = ""
        for iterator in newVariables:
            tempStrForNewVariables += iterator+","
        newPredicate = splitPredicateForCreatingNewOne[0] + "(" + tempStrForNewVariables[:len(tempStrForNewVariables)-1] + ")"
    return newPredicate

def unifyMaster(firstToCheck,secondToCheck,firstIsList,secondIsList):
    dictionary = {}
    if firstIsList == True and secondIsList == True:
        for iterator in firstToCheck:
            if iterator != '|' and iterator != '&' and iterator != '~':
                if len(iterator) == 2 and type(iterator) == list:
                    tempSplitOne = splitThePredicate(iterator[1])
                elif type(iterator) == str :
                    tempSplitOne = splitThePredicate(iterator)
                for subiterator in secondToCheck:
                    if subiterator != '|' and subiterator != '&' and subiterator != '~':
                        if len(subiterator) == 2 and type(subiterator) == list:
                            tempSplitTwo = splitThePredicate(subiterator[1])
                        elif type(subiterator) == str :
                            tempSplitTwo = splitThePredicate(subiterator)

                    if tempSplitOne[0] == tempSplitTwo[0]:
                        # print tempSplitOne , tempSplitTwo
                        retCode,dictionary = unify(tempSplitOne[1],tempSplitTwo[1],dictionary)
                        return dictionary
    elif firstIsList == True and secondIsList == False:
        if len(secondToCheck) == 2 and type(secondToCheck) == list:
            tempSplitTwo = splitThePredicate(secondToCheck[1])
        elif type(secondToCheck) == str and secondToCheck != '|' and secondToCheck != '&' and secondToCheck != '~':
            tempSplitTwo = splitThePredicate(secondToCheck)
        for iterator in firstToCheck:
            if iterator != '|' and iterator != '&' and iterator != '~':
                if len(iterator) == 2 and type(iterator) == list:
                    tempSplitOne = splitThePredicate(iterator[1])
                elif type(iterator) == str :
                    tempSplitOne = splitThePredicate(iterator)
                if tempSplitOne[0] == tempSplitTwo[0]:
                    retCode,dictionary = unify(tempSplitOne[1],tempSplitTwo[1],dictionary)
                    return dictionary
    elif secondIsList == True and firstIsList == False:
        if len(firstToCheck) == 2 and type(firstToCheck) == list:
            tempSplitOne = splitThePredicate(firstToCheck[1])
        elif type(firstToCheck) == str:
            tempSplitOne = splitThePredicate(firstToCheck)
        for iterator in secondToCheck:
            if iterator != '|' and iterator != '&' and iterator != '~':
                if len(iterator) == 2 and type(iterator) == list:
                    tempSplitTwo = splitThePredicate(iterator[1])
                elif type(iterator) == str:
                    tempSplitTwo = splitThePredicate(iterator)
                if tempSplitOne[0] == tempSplitTwo[0]:
                    retCode,dictionary = unify(tempSplitOne[1],tempSplitTwo[1],dictionary)
                    return dictionary
    else:
        if len(firstToCheck) == 2 and type(firstToCheck) == list:
            tempSplitOne = splitThePredicate(firstToCheck[1])
        elif type(firstToCheck) == str:
            tempSplitOne = splitThePredicate(firstToCheck)
        if len(secondToCheck) == 2 and type(secondToCheck) == list:
            tempSplitTwo = splitThePredicate(secondToCheck[1])
        elif type(secondToCheck) == str:
            tempSplitTwo = splitThePredicate(secondToCheck)
        if tempSplitOne[0] == tempSplitTwo[0]:
            retCode, dictionary = unify(tempSplitOne[1], tempSplitTwo[1], dictionary)
            return dictionary
    return dictionary

def resolveFurtherBruteForceOrignalVersionOne(first,second):
    newPredicate = []
    # Before sending to resolveFurther check if this can be reesolved "Duh..!!"
    # again the regular 3 cases needs to be checked
    # When do we need to send?
    # First - Both are a list > size 3 and one of them contains a positive predidcate and the other contains a negative predicate
    # Second - One if a list > size 3 and the other is a string check for +ve and -ve combination here
    # Third - One is a -ve predicate and the other is a +ve predicate
    firstIsList = False
    secondIsList = False
    firstToCheck = first
    secondToCheck = second
    checkToResolve = False
    if list == type(firstToCheck) and list == type(secondToCheck) and 3 <= len(firstToCheck) and 3 <= len(secondToCheck):
        firstIsList = True
        secondIsList = True
        for tempIterator in firstToCheck:
            if checkToResolve == True:
                break
            for tempSubIterator in secondToCheck:
                if (list == type(tempIterator) and 2 == len(tempIterator) and str == type(tempSubIterator)) and \
                         tempSubIterator != '|' and tempSubIterator != '&' and tempSubIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator[1])
                    tempOfSecond = splitThePredicate(tempSubIterator)
                    if tempOfFirst[0] == tempOfSecond[0]:
                        checkToResolve = True
                        #Now unify
                        # dictionary = unifyMaster(firstToCheck,secondToCheck,True,True)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        copyOfFirst     = replaceVariableInAPredicate(firstToCheck,dictionary)
                        copyOfSecond    = replaceVariableInAPredicate(secondToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        for newIterator in copyOfFirst:
                            if newIterator != '|' and splitThePredicate(newIterator)[0] != splitThePredicate(tempIterator)[0]\
                                    and splitThePredicate(newIterator)[0] != splitThePredicate(tempSubIterator)[0]:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                        for newIterator in copyOfSecond:
                            if newIterator != '|' and splitThePredicate(newIterator)[0] != splitThePredicate(tempIterator)[0]\
                                    and splitThePredicate(newIterator)[0] != splitThePredicate(tempSubIterator)[0]:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                        return newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1]

                elif (list == type(tempSubIterator) and 2 == len(tempSubIterator) and str == type(tempIterator)) and \
                         tempIterator != '|' and tempIterator != '&' and tempIterator != '~' :
                    tempOfFirst = splitThePredicate(tempIterator)
                    tempOfSecond = splitThePredicate(tempSubIterator[1])
                    if tempOfFirst[0] == tempOfSecond[0]:
                        checkToResolve = True
                        #Now unify
                        # dictionary = unifyMaster(firstToCheck,secondToCheck,True,True)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        copyOfFirst     = replaceVariableInAPredicate(firstToCheck,dictionary)
                        copyOfSecond    = replaceVariableInAPredicate(secondToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        for newIterator in copyOfFirst:
                            if newIterator != '|' and splitThePredicate(newIterator)[0] != splitThePredicate(tempIterator)[0]\
                                    and splitThePredicate(newIterator)[0] != splitThePredicate(tempSubIterator)[0]:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                        for newIterator in copyOfSecond:
                            if newIterator != '|' and splitThePredicate(newIterator)[0] != splitThePredicate(tempIterator)[0] and \
                                            splitThePredicate(newIterator)[0] != splitThePredicate(tempSubIterator)[0]:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                        return newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1]

    elif list == type(firstToCheck) and len(firstToCheck) >= 3 and \
            ((list == type(secondToCheck) and len(secondToCheck) == 2) or (type(secondToCheck) == str)):
        firstIsList = True
        if type(secondToCheck) == list:
            tempOfSecond = splitThePredicate(secondToCheck[1])
            for tempIterator in firstToCheck:
                if type(tempIterator) == str and tempIterator != '|' and tempIterator != '&' and tempIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator)
                    if tempOfSecond[0] == tempOfFirst[0]:
                        checkToResolve = True
                        # dictionary = unifyMaster(firstToCheck, secondToCheck, True, False)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        copyOfFirst     = replaceVariableInAPredicate(firstToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        for newIterator in copyOfFirst:
                            if newIterator != '|' and splitThePredicate(newIterator)[0] != splitThePredicate(tempIterator)[0]:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                        return newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1]



        elif type(secondToCheck) == str:
            tempOfSecond = splitThePredicate(secondToCheck)
            for tempIterator in firstToCheck:
                if type(tempIterator) == list and len(tempIterator) == 2 and\
                                tempIterator != '|' and tempIterator != '&' and tempIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator[1])
                    if tempOfSecond[0] == tempOfFirst[0]:
                        checkToResolve = True
                        # dictionary = unifyMaster(firstToCheck, secondToCheck, True, False)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        copyOfFirst     = replaceVariableInAPredicate(firstToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        for newIterator in copyOfFirst:
                            if newIterator != '|' and splitThePredicate(newIterator)[0] != splitThePredicate(tempIterator)[0]:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                        return newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1]


    elif list == type(secondToCheck) and len(secondToCheck) >= 3 and \
            ((list == type(firstToCheck) and len(firstToCheck) == 2) or (type(firstToCheck) == str)):
        secondIsList = True
        if type(firstToCheck) == list:
            tempOfSecond = splitThePredicate(firstToCheck[1])
            for tempIterator in secondToCheck:
                if type(tempIterator) == str and tempIterator != '|' and tempIterator != '&' and tempIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator)
                    if tempOfSecond[0] == tempOfFirst[0]:
                        checkToResolve = True
                        # dictionary = unifyMaster(firstToCheck, secondToCheck, False, True)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        copyOfSecond     = replaceVariableInAPredicate(secondToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        for newIterator in copyOfSecond:
                            if newIterator != '|' and splitThePredicate(newIterator)[0] != splitThePredicate(tempIterator)[0]:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                        return newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1]

        elif type(firstToCheck) == str:
            tempOfSecond = splitThePredicate(firstToCheck)
            for tempIterator in secondToCheck:
                if type(tempIterator) == list and len(tempIterator) == 2 and tempIterator != '|' and\
                                tempIterator != '&' and tempIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator[1])
                    if tempOfSecond[0] == tempOfFirst[0]:
                        checkToResolve = True
                        # dictionary = unifyMaster(firstToCheck, secondToCheck, False, True)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        copyOfSecond     = replaceVariableInAPredicate(secondToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        for newIterator in copyOfSecond:
                            if newIterator != '|' and splitThePredicate(newIterator)[0] != splitThePredicate(tempIterator)[0]:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                        return newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1]
    elif type(firstToCheck) == str and type(secondToCheck) == list and len(secondToCheck) == 2:
        tempOfFirst = splitThePredicate(firstToCheck)
        tempOfSecond = splitThePredicate(secondToCheck[1])
        if tempOfFirst[0] == tempOfSecond[0]:
            checkToResolve = True
            return newPredicate
    elif type(secondToCheck) == str and type(firstToCheck) == list and len(firstToCheck) == 2:
        tempOfFirst = splitThePredicate(firstToCheck[1])
        tempOfSecond = splitThePredicate(secondToCheck)
        if tempOfFirst[0] == tempOfSecond[0]:
            checkToResolve = True
            return newPredicate
    return newPredicate

def resolveFurtherBruteForceNextVersion(first,second):
    newPredicate = []
    # Before sending to resolveFurther check if this can be reesolved "Duh..!!"
    # again the regular 3 cases needs to be checked
    # When do we need to send?
    # First - Both are a list > size 3 and one of them contains a positive predidcate and the other contains a negative predicate
    # Second - One if a list > size 3 and the other is a string check for +ve and -ve combination here
    # Third - One is a -ve predicate and the other is a +ve predicate
    firstIsList = False
    secondIsList = False
    firstToCheck = first
    secondToCheck = second
    checkToResolve = False
    if list == type(firstToCheck) and list == type(secondToCheck) and 3 <= len(firstToCheck) and 3 <= len(secondToCheck):
        firstIsList = True
        secondIsList = True
        for tempIterator in firstToCheck:
            if checkToResolve == True:
                break
            for tempSubIterator in secondToCheck:
                if (list == type(tempIterator) and 2 == len(tempIterator) and str == type(tempSubIterator)) and \
                         tempSubIterator != '|' and tempSubIterator != '&' and tempSubIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator[1])
                    tempOfSecond = splitThePredicate(tempSubIterator)
                    if tempOfFirst[0] == tempOfSecond[0]:
                        checkToResolve = True
                        #Now unify
                        # dictionary = unifyMaster(firstToCheck,secondToCheck,True,True)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        if dictionary == False:
                            continue
                        copyOfFirst     = replaceVariableInAPredicate(firstToCheck,dictionary)
                        copyOfSecond    = replaceVariableInAPredicate(secondToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        tempOfFirst = splitThePredicate(replaceVariableInAPredicate(tempIterator[1],dictionary))
                        tempOfSecond = splitThePredicate(replaceVariableInAPredicate(tempSubIterator,dictionary))
                        placeHolderOfTempIterator = firstToCheck.index(tempIterator)
                        placeHolderOfTempSubIterator = secondToCheck.index(tempSubIterator)
                        countForSkip = 0
                        for newIterator in copyOfFirst:
                            firstTemp = splitThePredicate(newIterator)
                            # if newIterator != '|' and ((firstTemp[0] != tempOfFirst[0]) or (firstTemp[0] == tempOfFirst[0] and firstTemp[1] != tempOfFirst[1]) )\
                            #                       and ((firstTemp[0] != tempOfSecond[0]) or (firstTemp[0] == tempOfSecond[0] and firstTemp[1] != tempOfSecond[1]) ):
                            if placeHolderOfTempIterator != countForSkip and newIterator != '|':
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                            countForSkip += 1
                        countForSkip = 0
                        for newIterator in copyOfSecond:
                            firstTemp = splitThePredicate(newIterator)
                            # if newIterator != '|' and ((firstTemp[0] != tempOfFirst[0]) or (firstTemp[0] == tempOfFirst[0] and firstTemp[1] != tempOfFirst[1]) )\
                            #                       and ((firstTemp[0] != tempOfSecond[0]) or (firstTemp[0] == tempOfSecond[0] and firstTemp[1] != tempOfSecond[1]) ):
                            if placeHolderOfTempSubIterator != countForSkip and newIterator != '|':
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                            countForSkip += 1
                        newPredicate.append( newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1])

                elif (list == type(tempSubIterator) and 2 == len(tempSubIterator) and str == type(tempIterator)) and \
                         tempIterator != '|' and tempIterator != '&' and tempIterator != '~' :
                    tempOfFirst = splitThePredicate(tempIterator)
                    tempOfSecond = splitThePredicate(tempSubIterator[1])
                    if tempOfFirst[0] == tempOfSecond[0]:
                        checkToResolve = True
                        #Now unify
                        # dictionary = unifyMaster(firstToCheck,secondToCheck,True,True)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        if dictionary == False:
                            continue
                        copyOfFirst     = replaceVariableInAPredicate(firstToCheck,dictionary)
                        copyOfSecond    = replaceVariableInAPredicate(secondToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        tempOfFirst = splitThePredicate(replaceVariableInAPredicate(tempIterator,dictionary))
                        tempOfSecond = splitThePredicate(replaceVariableInAPredicate(tempSubIterator[1],dictionary))
                        placeHolderOfTempIterator = firstToCheck.index(tempIterator)
                        placeHolderOfTempSubIterator = secondToCheck.index(tempSubIterator)
                        countForSkip = 0
                        for newIterator in copyOfFirst:
                            firstTemp = splitThePredicate(newIterator)
                            # if newIterator != '|' and ((firstTemp[0] != tempOfFirst[0]) or (firstTemp[0] == tempOfFirst[0] and firstTemp[1] != tempOfFirst[1]) )\
                            #                       and ((firstTemp[0] != tempOfSecond[0]) or (firstTemp[0] == tempOfSecond[0] and firstTemp[1] != tempOfSecond[1]) ):
                            if placeHolderOfTempIterator != countForSkip and newIterator != '|':
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                            countForSkip += 1
                        countForSkip = 0
                        for newIterator in copyOfSecond:
                            firstTemp = splitThePredicate(newIterator)
                            # if newIterator != '|' and ((firstTemp[0] != tempOfFirst[0]) or (firstTemp[0] == tempOfFirst[0] and firstTemp[1] != tempOfFirst[1]) )\
                            #                       and ((firstTemp[0] != tempOfSecond[0]) or (firstTemp[0] == tempOfSecond[0] and firstTemp[1] != tempOfSecond[1]) ):
                            if placeHolderOfTempSubIterator != countForSkip and newIterator != '|':
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                            countForSkip += 1
                        newPredicate.append( newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1])

    elif list == type(firstToCheck) and len(firstToCheck) >= 3 and \
            ((list == type(secondToCheck) and len(secondToCheck) == 2) or (type(secondToCheck) == str)):
        firstIsList = True
        if type(secondToCheck) == list:
            tempOfSecond = splitThePredicate(secondToCheck[1])
            for tempIterator in firstToCheck:
                if type(tempIterator) == str and tempIterator != '|' and tempIterator != '&' and tempIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator)
                    if tempOfSecond[0] == tempOfFirst[0]:
                        checkToResolve = True
                        # dictionary = unifyMaster(firstToCheck, secondToCheck, True, False)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        if dictionary == False:
                            continue
                        copyOfFirst     = replaceVariableInAPredicate(firstToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        placeHolderOfTempIterator = firstToCheck.index(tempIterator)
                        # tempOfFirst = splitThePredicate(replaceVariableInAPredicate(tempIterator,dictionary))
                        countForSkip = 0
                        for newIterator in copyOfFirst:
                            firstTemp = splitThePredicate(newIterator)
                            # if newIterator != '|' and ((firstTemp[0] != tempOfFirst[0]) or (firstTemp[0] == tempOfFirst[0] \
                            #                                                                 and firstTemp[1] != tempOfFirst[1])  ):
                            if newIterator != '|' and countForSkip != placeHolderOfTempIterator:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                            countForSkip += 1
                        newPredicate.append( newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1])



        elif type(secondToCheck) == str:
            tempOfSecond = splitThePredicate(secondToCheck)
            for tempIterator in firstToCheck:
                if type(tempIterator) == list and len(tempIterator) == 2 and\
                                tempIterator != '|' and tempIterator != '&' and tempIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator[1])
                    if tempOfSecond[0] == tempOfFirst[0]:
                        checkToResolve = True
                        # dictionary = unifyMaster(firstToCheck, secondToCheck, True, False)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        if dictionary == False:
                            continue
                        copyOfFirst     = replaceVariableInAPredicate(firstToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        # tempOfFirst = splitThePredicate(replaceVariableInAPredicate(tempIterator[1], dictionary))
                        placeHolderOfTempIterator = firstToCheck.index(tempIterator)
                        countForSkip = 0
                        for newIterator in copyOfFirst:
                            firstTemp = splitThePredicate(newIterator)
                            # if newIterator != '|' and ((firstTemp[0] != tempOfFirst[0]) or (firstTemp[0] == tempOfFirst[0] \
                            #                                                                 and firstTemp[1] != tempOfFirst[1])  ):
                            if newIterator != '|' and countForSkip != placeHolderOfTempIterator:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                            countForSkip += 1
                        newPredicate.append( newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1])


    elif list == type(secondToCheck) and len(secondToCheck) >= 3 and \
            ((list == type(firstToCheck) and len(firstToCheck) == 2) or (type(firstToCheck) == str)):
        secondIsList = True
        if type(firstToCheck) == list:
            tempOfSecond = splitThePredicate(firstToCheck[1])
            for tempIterator in secondToCheck:
                if type(tempIterator) == str and tempIterator != '|' and tempIterator != '&' and tempIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator)
                    if tempOfSecond[0] == tempOfFirst[0]:
                        checkToResolve = True
                        # dictionary = unifyMaster(firstToCheck, secondToCheck, False, True)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        if dictionary == False:
                            continue
                        copyOfSecond     = replaceVariableInAPredicate(secondToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        # tempOfFirst = splitThePredicate(replaceVariableInAPredicate(tempIterator, dictionary))
                        placeHolderOfTempIterator = secondToCheck.index(tempIterator)
                        countForSkip = 0
                        for newIterator in copyOfSecond:
                            firstTemp = splitThePredicate(newIterator)
                            # if newIterator != '|' and ((firstTemp[0] != tempOfFirst[0]) or (firstTemp[0] == tempOfFirst[0] \
                            #                                                                 and firstTemp[1] != tempOfFirst[1])  ):
                            if newIterator != '|' and countForSkip != placeHolderOfTempIterator:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                            countForSkip += 1
                        newPredicate.append( newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1])

        elif type(firstToCheck) == str:
            tempOfSecond = splitThePredicate(firstToCheck)
            for tempIterator in secondToCheck:
                if type(tempIterator) == list and len(tempIterator) == 2 and tempIterator != '|' and\
                                tempIterator != '&' and tempIterator != '~':
                    tempOfFirst = splitThePredicate(tempIterator[1])
                    if tempOfSecond[0] == tempOfFirst[0]:
                        checkToResolve = True
                        # dictionary = unifyMaster(firstToCheck, secondToCheck, False, True)
                        dictionary = {}
                        dictionary = newUnify(tempOfFirst[1], tempOfSecond[1],dictionary)
                        if dictionary == False:
                            continue
                        copyOfSecond     = replaceVariableInAPredicate(secondToCheck,dictionary)
                        newTempPredicateToWorkOn = []
                        # tempOfFirst = splitThePredicate(replaceVariableInAPredicate(tempIterator[1], dictionary))
                        placeHolderOfTempIterator = secondToCheck.index(tempIterator)
                        countForSkip = 0
                        for newIterator in copyOfSecond:
                            firstTemp = splitThePredicate(newIterator)
                            # if newIterator != '|' and  ((firstTemp[0] != tempOfFirst[0]) or (firstTemp[0] == tempOfFirst[0] \
                            #                                                                 and firstTemp[1] != tempOfFirst[1])  ):
                            if newIterator != '|' and countForSkip != placeHolderOfTempIterator:
                                newTempPredicateToWorkOn.append(newIterator)
                                newTempPredicateToWorkOn.append('|')
                            countForSkip += 1
                        newPredicate.append( newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn)-1])
    elif type(firstToCheck) == str and type(secondToCheck) == list and len(secondToCheck) == 2:
        tempOfFirst = splitThePredicate(firstToCheck)
        tempOfSecond = splitThePredicate(secondToCheck[1])
        if tempOfFirst[0] == tempOfSecond[0]:
            checkToResolve = True
            dictionary = {}
            dictionary = newUnify(tempOfFirst[1], tempOfSecond[1], dictionary)
            if dictionary == False:
                return None
            return newPredicate
    elif type(secondToCheck) == str and type(firstToCheck) == list and len(firstToCheck) == 2:
        tempOfFirst = splitThePredicate(firstToCheck[1])
        tempOfSecond = splitThePredicate(secondToCheck)
        if tempOfFirst[0] == tempOfSecond[0]:
            checkToResolve = True
            dictionary = {}
            dictionary = newUnify(tempOfFirst[1], tempOfSecond[1], dictionary)
            if dictionary == False:
                return None
            return newPredicate
    if len(newPredicate) == 0:
        return None
    return newPredicate

def checkIfPresentInKBMaster(statement,KBList):
    for iterator in KBList:
        if dedup(iterator,statement) == True:
            return True
    return False


def checkIfPresentInKB(list1,list2):
    #3 cases
    # Case 1 : Both are string then check them
    # Case 2: Both are negated string then check them
    # Case 3 : Both are list then check one by one
    if type(list1) == str and type(list2) == str:
        if list1 == list2:
            return True
    elif type(list1) == list and type(list2) == list and \
        len(list1) == 2 and len(list2) == 2 and\
        list1[0] == '~' and list2[0] == '~' and\
            type(list1[1]) == type(list2[1]) and type(list1[1]) == str:
        if list1[1] == list2[1]:
            return True
    elif type(list1) == type(list2) and type(list1) == list1 and\
        len(list1) >= 3 and len(list2) >=3 and len(list1) == len(list2):
        for iterator in list1:
            if iterator not in list2:
                return False
        for iterator in list2:
            if iterator not in list1:
                return False
        return True
    else:
        return False
    return False





def resolution(KBList,statement):
    KBListToActOn = copy.copy(KBList)
    #Convert the "statement" to CNF
    parser = yacc.yacc()
    lexer = lex.lex()
    temp = statement.replace(" ", "")
    temp = parser.parse(temp, lexer)
    temp = removeImply(temp)
    temp = moveNotInwards(temp)
    temp = reduceTheKB(temp)
    temp = removeInnerBracket(temp)
    temp = refuteNewClause(temp)
    count = 1
    #Add the refuted statement into the new KB List
    KBListToActOn.insert(0,temp)
    newSetToActOn = set()
    print "Done Processing KB"
    while True:
        lengthOfTheKB = len(KBListToActOn)
        newPairsToCheck = []
        superCounter = 0
        print 'Setting Supercounter to  0'
        for iterator in range(0,lengthOfTheKB):
            for subiterator in range(iterator+1,lengthOfTheKB):
                newPairsToCheck.append((KBListToActOn[iterator],KBListToActOn[subiterator]))
        resolve = []
        print len(newPairsToCheck), 'this is something'
        #Resolve
        for iterator in range(0,len(newPairsToCheck)):
            print iterator,'iterator'
            print len(newPairsToCheck)
            count += 1
            # print count
            if count == 47:
                print "h"
            print "unifying " +  str(newPairsToCheck[iterator][0]) + " and " + str(newPairsToCheck[iterator][1])
            answer = resolveFurtherBruteForceNextVersion(newPairsToCheck[iterator][0], newPairsToCheck[iterator][1])
            if type(answer) == list:
                print len(answer),'Answer length'
            else:
                print 'other case'
            if answer == None:
                continue
            elif len(answer) == 0:
                return True
            for answerIterator in answer:
                answerIterator = answer[0] if type(answerIterator) == list and len(answerIterator) == 2 and ((type(answerIterator[0]) == str)\
                                        or\
                                      (type(answerIterator[0]) == list and len(answerIterator[0]) == 2  and type(answerIterator[0][1]) == str)) else answerIterator
                answerIterator = answerIterator[0] if type(answerIterator) == list and len(answerIterator) == 1 else answerIterator
                #Check if the KB is present in the DB
                # isPresentInKB = checkIfPresentInKB(answerIterator,KBListToActOn)
                if answerIterator in KBListToActOn and len(answerIterator) > 0:
                    superCounter +=1
                    print 'Incrementing Super Counter',superCounter
                    resolve.append(answerIterator)
                    # print "--------------------"
                    print "Answer " + str(answerIterator)
                    # print "--------------------"
                #Check the facts
                if type(answerIterator) == str :
                    variablesOfAnswer = splitThePredicate(answerIterator)
                    isFact = True
                    for superAnswerIterator in variablesOfAnswer[1]:
                        if superAnswerIterator[0].islower() == True:
                            isFact = False
                            break
                    if isFact == True and ['~',answerIterator] in KBListToActOn:
                        return True
                if type(answerIterator) == list and len(answerIterator) == 2 and answerIterator[0] == '~' and type(answerIterator[1]) == str  :
                    variablesOfAnswer = splitThePredicate(answerIterator[1])
                    isFact = True
                    for superAnswerIterator in variablesOfAnswer[1]:
                        if superAnswerIterator[0].islower() == True:
                            isFact = False
                            break
                    if isFact == True and answerIterator[1] in KBListToActOn:
                        return True


        if superCounter == 0:
            return False
        print  'Adding', len(resolve)
        print "Current" , len(KBListToActOn)
        KBListToActOn.extend(resolve)
        print "new KB List" , len(KBListToActOn)


def refuteNewPredicate(x):
    if type(x) == str:
        return ['~',x]
    elif type(x) == list and len(x) == 2 and x[0] == '~':
        return x[1]
    elif type(x) == list:
        output = []
        for iterator in x:
            if iterator == '|':
                output.append('&')
            elif list == type(iterator) and 2 == len(iterator) and '~' == iterator[0]:
                output.append(iterator[1])
            elif str == type(iterator):
                output.append(['~',iterator])
        return output

def resolutionBFS(KBList,statement,tableIndexPositive,tableIndexNegative):
    KBListToActOn = copy.copy(KBList)
    # Convert the "statement" to CNF
    parser = yacc.yacc()
    lexer = lex.lex()
    temp = statement.replace(" ", "")
    temp = parser.parse(temp, lexer)
    temp = removeImply(temp)
    temp = moveNotInwards(temp)
    temp = reduceTheKB(temp)
    temp = removeInnerBracket(temp)
    temp = refuteNewClause(temp)
    count = 1
    # Add the refuted statement into the new KB List
    KBListToActOn.append(temp)
    count = 0
    while True:
        # print count
        # count += 1
        # if count == 0:
            # print ""
        print len(KBListToActOn)
        superCounter  = 0
        newList = []
        counter = 1
        for iterator in KBListToActOn:
            # if counter == 8:
            #     print ""
            # print counter
            counter += 1
            if iterator != '~' and iterator != '&' and iterator != "|":
                #Handle here for string and negated list
                if type(iterator) == str :
                    tempAtomicSubIterator = splitThePredicate(iterator)
                    isNegated = False
                    #Get the index List
                    listOfIndex = None
                    listOfIndex = tableIndexNegative[tempAtomicSubIterator[0]]
                    tempList = []
                    for indexIterator in listOfIndex:
                            print "Unifying Predicates" , str(iterator) , KBListToActOn[indexIterator]
                            answer = resolveFurtherBruteForceNextVersion(iterator,KBListToActOn[indexIterator])
                            #answer can have 3 cases
                            #1) Null set -> then return True
                            #2) None -> Then continue cannot be unified
                            #3) List -> A derived KB
                            if answer == None:
                                continue
                            elif len(answer) == 0:
                                return True
                            else:
                                tempList.append(answer)

                elif (type(iterator) == list and len(iterator) == 2 and iterator[0] == '~'):
                    tempAtomicSubIterator = splitThePredicate(iterator[1])
                    isNegated = True
                    # Get the index List
                    listOfIndex = None
                    listOfIndex = tableIndexPositive[tempAtomicSubIterator[0]]
                    tempList = []
                    for indexIterator in listOfIndex:
                        print "Unifying Predicates", str(iterator), KBListToActOn[indexIterator]
                        answer = resolveFurtherBruteForceNextVersion(iterator, KBListToActOn[indexIterator])
                        # answer can have 3 cases
                        # 1) Null set -> then return True
                        # 2) None -> Then continue cannot be unified
                        # 3) List -> A derived KB
                        if answer == None:
                            continue
                        elif len(answer) == 0:
                            return True
                        else:
                            tempList.append(answer)
                else:
                    #This is for regular list
                    for subiterator in iterator:
                        if subiterator != '~' and subiterator != '&' and subiterator != "|":
                            #Split the predicate
                            if type(subiterator) == str:
                                tempAtomicSubIterator = splitThePredicate(subiterator)
                                isNegated = False
                            elif type(subiterator) == list and len(subiterator) == 2:
                                tempAtomicSubIterator = splitThePredicate(subiterator[1])
                                isNegated = True

                            #Get the index List
                            listOfIndex = None
                            if isNegated == True:
                                listOfIndex = tableIndexPositive[tempAtomicSubIterator[0]]
                            else:
                                listOfIndex = tableIndexNegative[tempAtomicSubIterator[0]]

                            tempList = []
                            if listOfIndex != None:
                                for indexIterator in listOfIndex:
                                    print "Unifying Predicates", str(iterator), KBListToActOn[indexIterator]
                                    answer = resolveFurtherBruteForceNextVersion(iterator,KBListToActOn[indexIterator])
                                    #answer can have 3 cases
                                    #1) Null set -> then return True
                                    #2) None -> Then continue cannot be unified
                                    #3) List -> A derived KB
                                    if answer == None:
                                        continue
                                    elif len(answer) == 0:
                                        return True
                                    else:
                                        tempList.append(answer)

            #Handle the validation for answers code here
            #3 Cases to be handeled
            # 1)The new ~KB is there in the KB then Return True
            # 2) The new kb is there in the KB then continue
            # 3) Else add the fact to the main KB and then update the super counter
            for superAnswer in tempList:
                    for answerIterator in superAnswer:
                        answerIterator = answerIterator[0] if type(answerIterator) == list and len(answerIterator) == 2 and (
                            (type(answerIterator[0]) == str) \
                        or \
                        (type(answerIterator[0]) == list and len(answerIterator[0]) == 2 and type(
                            answerIterator[0][1]) == str)) else answerIterator
                        answerIterator = answerIterator[0] if type(answerIterator) == list and len(
                            answerIterator) == 1 else answerIterator

                        #Handling case 1 here......
                        # Check the facts
                        if type(answerIterator) == str:
                            variablesOfAnswer = splitThePredicate(answerIterator)
                            isFact = True
                            for superAnswerIterator in variablesOfAnswer[1]:
                                if superAnswerIterator[0].islower() == True:
                                    isFact = False
                                    break
                            if isFact == True and ['~', answerIterator] in KBListToActOn:
                                return True
                        if type(answerIterator) == list and len(answerIterator) == 2 and answerIterator[
                            0] == '~' and type(answerIterator[1]) == str:
                            variablesOfAnswer = splitThePredicate(answerIterator[1])
                            isFact = True
                            for superAnswerIterator in variablesOfAnswer[1]:
                                if superAnswerIterator[0].islower() == True:
                                    isFact = False
                                    break
                            if isFact == True and answerIterator[1] in KBListToActOn:
                                return True

                        # Handling case 2 & 3 here......
                        isPresentInKB = checkIfPresentInKBMaster(answerIterator, KBListToActOn)
                        # if isPresentInKB
                        # if answerIterator not in KBListToActOn and len(answerIterator) > 0:
                        if isPresentInKB == False and len(answerIterator) > 0:
                            superCounter += 1
                            newList.append(answerIterator)
                            # print "--------------------"
                            print "Answer " + str(answerIterator)
                            # print "--------------------"
        if superCounter == 0:
            return False
        KBListToActOn.extend(newList)
        tableIndexPositive = defaultdict(list)
        tableIndexNegative = defaultdict(list)
        tableIndexPositive, tableIndexNegative = buildTableIndexing(KBList, tableIndexPositive, tableIndexNegative)

def resolutionSOS(KBList, statement, tableIndexPositive, tableIndexNegative):
        KBListToActOn = copy.copy(KBList)
        # Convert the "statement" to CNF
        parser = yacc.yacc()
        lexer = lex.lex()
        temp = statement.replace(" ", "")
        temp = parser.parse(temp, lexer)
        temp = removeImply(temp)
        temp = moveNotInwards(temp)
        temp = reduceTheKB(temp)
        temp = removeInnerBracket(temp)
        temp = refuteNewClause(temp)
        count = 1
        clause = temp

        #Try to Unify the clause with the KB
        atomicClause = splitThePredicate(clause)[0]
        #Get the index
        if type(clause) == str:
            listOfIndex = tableIndexNegative[atomicClause[0]]
        else:
            listOfIndex = tableIndexPositive[atomicClause[0]]
        sosList = []
        tempList = []
        for kbIterator in listOfIndex:
            answer = resolveFurtherBruteForceNextVersion(clause, KBListToActOn[kbIterator])
            # answer can have 3 cases
            # 1) Null set -> then return True
            # 2) None -> Then continue cannot be unified
            # 3) List -> A derived KB
            if answer == None:
                continue
            elif len(answer) == 0:
                return True
            else:
                tempList.append(answer)

        # Handle the validation for answers code here
        # 3 Cases to be handeled
        # 1)The new ~KB is there in the KB then Return True
        # 2) The new kb is there in the KB then continue
        # 3) Else add the fact to the main KB and then update the super counter
        for superAnswer in tempList:
            for answerIterator in superAnswer:
                answerIterator = answerIterator[0] if type(answerIterator) == list and len(
                    answerIterator) == 2 and (
                                                          (type(answerIterator[0]) == str) \
                                                          or \
                                                          (type(answerIterator[0]) == list and len(
                                                              answerIterator[0]) == 2 and type(
                                                              answerIterator[0][1]) == str)) else answerIterator
                answerIterator = answerIterator[0] if type(answerIterator) == list and len(
                    answerIterator) == 1 else answerIterator

                # Handling case 1 here......
                # Check the facts
                if type(answerIterator) == str:
                    variablesOfAnswer = splitThePredicate(answerIterator)
                    isFact = True
                    for superAnswerIterator in variablesOfAnswer[1]:
                        if superAnswerIterator[0].islower() == True:
                            isFact = False
                            break
                    if isFact == True and ['~', answerIterator] in KBListToActOn:
                        return True
                if type(answerIterator) == list and len(answerIterator) == 2 and answerIterator[
                    0] == '~' and type(answerIterator[1]) == str:
                    variablesOfAnswer = splitThePredicate(answerIterator[1])
                    isFact = True
                    for superAnswerIterator in variablesOfAnswer[1]:
                        if superAnswerIterator[0].islower() == True:
                            isFact = False
                            break
                    if isFact == True and answerIterator[1] in KBListToActOn:
                        return True

                # Handling case 2 & 3 here......
                isPresentInKB = checkIfPresentInKBMaster(answerIterator, KBListToActOn)
                # if isPresentInKB
                # if answerIterator not in KBListToActOn and len(answerIterator) > 0:
                if isPresentInKB == False and len(answerIterator) > 0:
                    sosList.append(answerIterator)
                    # print "--------------------"
                    print "Answer " + str(answerIterator)
                    # print "--------------------"

        if len(sosList) == 0:
            return False
        KBListToActOn.extend(sosList)
        tableIndexPositive, tableIndexNegative = buildTableIndexing(KBList, tableIndexPositive, tableIndexNegative)

        # Add the refuted statement into the new KB List
        KBListToActOn.append(clause)
        count = 0
        while True:
            # print count
            # count += 1
            # if count == 0:
            # print ""
            print len(KBListToActOn)
            superCounter = 0
            newList = []
            counter = 1
            for iterator in sosList:
                # if counter == 8:
                #     print ""
                # print counter
                counter += 1
                if iterator != '~' and iterator != '&' and iterator != "|":
                    # Handle here for string and negated list
                    if type(iterator) == str:
                        tempAtomicSubIterator = splitThePredicate(iterator)
                        isNegated = False
                        # Get the index List
                        listOfIndex = None
                        listOfIndex = tableIndexNegative[tempAtomicSubIterator[0]]
                        tempList = []
                        for indexIterator in listOfIndex:
                            print "Unifying Predicates", str(iterator), KBListToActOn[indexIterator]
                            answer = resolveFurtherBruteForceNextVersion(iterator, KBListToActOn[indexIterator])
                            # answer can have 3 cases
                            # 1) Null set -> then return True
                            # 2) None -> Then continue cannot be unified
                            # 3) List -> A derived KB
                            if answer == None:
                                continue
                            elif len(answer) == 0:
                                return True
                            else:
                                tempList.append(answer)

                    elif (type(iterator) == list and len(iterator) == 2 and iterator[0] == '~'):
                        tempAtomicSubIterator = splitThePredicate(iterator[1])
                        isNegated = True
                        # Get the index List
                        listOfIndex = None
                        listOfIndex = tableIndexPositive[tempAtomicSubIterator[0]]
                        tempList = []
                        for indexIterator in listOfIndex:
                            print "Unifying Predicates", str(iterator), KBListToActOn[indexIterator]
                            answer = resolveFurtherBruteForceNextVersion(iterator, KBListToActOn[indexIterator])
                            # answer can have 3 cases
                            # 1) Null set -> then return True
                            # 2) None -> Then continue cannot be unified
                            # 3) List -> A derived KB
                            if answer == None:
                                continue
                            elif len(answer) == 0:
                                return True
                            else:
                                tempList.append(answer)
                    else:
                        # This is for regular list
                        for subiterator in iterator:
                            if subiterator != '~' and subiterator != '&' and subiterator != "|":
                                # Split the predicate
                                if type(subiterator) == str:
                                    tempAtomicSubIterator = splitThePredicate(subiterator)
                                    isNegated = False
                                elif type(subiterator) == list and len(subiterator) == 2:
                                    tempAtomicSubIterator = splitThePredicate(subiterator[1])
                                    isNegated = True

                                # Get the index List
                                listOfIndex = None
                                if isNegated == True:
                                    listOfIndex = tableIndexPositive[tempAtomicSubIterator[0]]
                                else:
                                    listOfIndex = tableIndexNegative[tempAtomicSubIterator[0]]

                                tempList = []
                                if listOfIndex != None:
                                    for indexIterator in listOfIndex:
                                        print "Unifying Predicates", str(iterator), KBListToActOn[indexIterator]
                                        answer = resolveFurtherBruteForceNextVersion(iterator,
                                                                                     KBListToActOn[indexIterator])
                                        # answer can have 3 cases
                                        # 1) Null set -> then return True
                                        # 2) None -> Then continue cannot be unified
                                        # 3) List -> A derived KB
                                        if answer == None:
                                            continue
                                        elif len(answer) == 0:
                                            return True
                                        else:
                                            tempList.append(answer)

                # Handle the validation for answers code here
                # 3 Cases to be handeled
                # 1)The new ~KB is there in the KB then Return True
                # 2) The new kb is there in the KB then continue
                # 3) Else add the fact to the main KB and then update the super counter
                for superAnswer in tempList:
                    for answerIterator in superAnswer:
                        answerIterator = answerIterator[0] if type(answerIterator) == list and len(
                            answerIterator) == 2 and (
                                                                  (type(answerIterator[0]) == str) \
                                                                  or \
                                                                  (type(answerIterator[0]) == list and len(
                                                                      answerIterator[0]) == 2 and type(
                                                                      answerIterator[0][1]) == str)) else answerIterator
                        answerIterator = answerIterator[0] if type(answerIterator) == list and len(
                            answerIterator) == 1 else answerIterator

                        # Handling case 1 here......
                        # Check the facts
                        if type(answerIterator) == str:
                            variablesOfAnswer = splitThePredicate(answerIterator)
                            isFact = True
                            for superAnswerIterator in variablesOfAnswer[1]:
                                if superAnswerIterator[0].islower() == True:
                                    isFact = False
                                    break
                            if isFact == True and ['~', answerIterator] in KBListToActOn:
                                return True
                        if type(answerIterator) == list and len(answerIterator) == 2 and answerIterator[
                            0] == '~' and type(answerIterator[1]) == str:
                            variablesOfAnswer = splitThePredicate(answerIterator[1])
                            isFact = True
                            for superAnswerIterator in variablesOfAnswer[1]:
                                if superAnswerIterator[0].islower() == True:
                                    isFact = False
                                    break
                            if isFact == True and answerIterator[1] in KBListToActOn:
                                return True

                        # Handling case 2 & 3 here......
                        isPresentInKB = checkIfPresentInKBMaster(answerIterator, KBListToActOn)
                        # if isPresentInKB
                        # if answerIterator not in KBListToActOn and len(answerIterator) > 0:
                        if isPresentInKB == False and len(answerIterator) > 0:
                            superCounter += 1
                            newList.append(answerIterator)
                            # print "--------------------"
                            print "Answer " + str(answerIterator)
                            # print "--------------------"
            if superCounter == 0:
                return False
            newList.extend(sosList)
            sosList = copy.copy(newList)
            tableIndexPositive = defaultdict(list)
            tableIndexNegative = defaultdict(list)
            tableIndexPositive, tableIndexNegative = buildTableIndexing(KBList, tableIndexPositive, tableIndexNegative)



#==========================================================================#
#Functions concentrated on working on KB and the algorithm


def dedup(x,y):
    if type(x) == str and type(y) == list:
        if x in y:
            return True
    if type(x) == str and type(y) == str:
        if x == y:
            return True
    if type(x) == list and len(x) ==2 and type(y) == list:
        if x in y:
            return  True
    if type(x) == list and len(x) == 2 and type(y) == list and len(y) == 2:
        if x == y:
            return True
    if type(x) == list and len(x)>2:
        bool_var = True
        for each_x in x:
            bool_var = bool_var and  dedup(each_x,y)
        return bool_var


#Start main function
#Goal is read statements one by one and then put it into KB
if __name__ == "__main__":
    #Initialize KB List
    KBList = []
    tableIndexPositive = defaultdict(list)
    tableIndexNegative = defaultdict(list)
    #read file from input.txt
    readFile()

    parser = yacc.yacc()
    lexer = lex.lex()
    #Find the starting point to start iterating
    startPoint = int(readFileList[0]) + 2
    for iterator in range(startPoint,len(readFileList)):
        #Steps that needs to be followed
        #1) Remove Implication
        #2) Move Not inwards
        #3) Distribute the logic if & and | combination is present
        #4) Remove all inner brackets
        #5) Put individual items into KB
        #6) Insert into KB
        #7) Create table based indexing in the program for two types of code, positive as well as negative
        temp = readFileList[iterator].replace(" ","")
        temp = parser.parse(temp,lexer)
        temp = removeImply(temp)
        temp = moveNotInwards(temp)
        temp = reduceTheKB(temp)
        temp = removeInnerBracket(temp)

        queue = []
        queue.append(temp)
        while(len(queue) != 0):
            temperory = queue.pop(0)
            if ((list == type(temperory) and temperory[1] == "|") or str == type(temperory)) or \
                    (list == type(temperory) and 2 == len(temperory)):
                KBList.append(temperory)
            else:
                for subiterator in range(0,len(temperory)):
                    if temperory[subiterator] != "|" and temperory[subiterator] != '&':
                        queue.append(temperory[subiterator])

    tableIndexPositive,tableIndexNegative = buildTableIndexing(KBList,tableIndexPositive,tableIndexNegative)
    #Standarize variables in KB
    #Send one KB at a time (2 Steps)
    #1) Remove all inner brackets and make it only or
    #2) Remove all variables and put new unique variables
    for iterator in range(0,len(KBList)):
        KBList[iterator] = removeAllInnerBracketForDisjunction(KBList[iterator])

    #Standarize variables in the KB
    #All variables inside a KB should be unique
    for iterator in range(0,len(KBList)):
        KBList[iterator] =  standarizeKB(KBList[iterator])

    for iterator in KBList:
        print str(iterator)
    # #unify
    firstToCheck = splitThePredicate("A(V,Bob)")
    secondToCheck = splitThePredicate("A(v1,Bob)")
    # print unifyMaster(firstToCheck,secondToCheck,True,True)
    # tempDict = {}
    # print newUnify(["z1","John"],["x2","x2"],tempDict) , "ankufbsdjvbfskvbkfbg"
    # tempDict = {}
    # print newUnify(["x2", "x2"],["z1", "John"],  tempDict), "ankufbsdjvbfskvbkfbg"
    r = []
    # Call resolution
    numberOfQueries = int(readFileList[0])
    for iterator in range(1,numberOfQueries+1):
        print "-----------" , readFileList[iterator]
        retCode = resolutionSOS(KBList,readFileList[iterator],tableIndexPositive,tableIndexNegative)
        r.append( retCode)
    # print r
    #
    # print dedup([['~', 'A'], 'B', ['~', 'C'], 'D'], [['~', 'C'], ['~', 'A'], 'D', 'B']), 'Suraj'

    # print resolveFurtherBruteForceNextVersion(["D(Bob,Bob)"] ,[["~","D(z,John)"], '|', "H(x)"]) , "Ankukr"
    # print resolveFurtherBruteForceNextVersion("A(Bob)" , [['~', 'A(x2)'], '|', 'D(x2,x2)'])