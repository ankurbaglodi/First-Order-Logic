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
        output.append(removeDistributionMaster([x[0][0], "|" , x[2][0]]))
        output.append("&")
        output.append(removeDistributionMaster([x[0][0], "|", x[2][2]]))
        output.append("&")
        output.append(removeDistributionMaster([x[0][2], "|", x[2][0]]))
        output.append("&")
        output.append(removeDistributionMaster([x[0][2], "|", x[2][2]]))
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
                    output.append(removeDistributionMaster([x[0][0], "|", x[2][0]]))
                    output.append("&")
                    output.append(removeDistributionMaster([x[0][0], "|", x[2][2]]))
                    output.append("&")
                    output.append(removeDistributionMaster([x[0][2], "|", x[2][0]]))
                    output.append("&")
                    output.append(removeDistributionMaster([x[0][2], "|", x[2][2]]))
                else:
                    #It will be in the same form as before
                    output.append(removeDistributionMaster([x[0][0] , "|" , x[2] ]))
                    output.append("&")
                    output.append(removeDistributionMaster([x[0][2], "|", x[2]]))
            else:
                # It will be in the same form as before
                output.append(removeDistributionMaster([x[0][0], "|", x[2]]))
                output.append("&")
                output.append(removeDistributionMaster([x[0][2], "|", x[2]]))

        #Handle third case
        elif "&" == x[2][1] and list == type(x[2]) :
                #Check if the following case is present
                # (a| (b&c)) | (c & d)
                if len(x[0]) == 3:
                    retCode = checkForDistribution(x[0])
                    if retCode:
                        x[0] = removeDistributionMaster(x[0])
                        #It will now convert to the same explanation as above
                        output.append(removeDistributionMaster([x[0][0], "|", x[2][0]]))
                        output.append(removeDistributionMaster([x[0][0], "|", x[2][2]]))
                        output.append("&")
                        output.append(removeDistributionMaster([x[0][2], "|", x[2][0]]))
                        output.append(removeDistributionMaster([x[0][2], "|", x[2][2]]))
                    else:
                        output.append(removeDistributionMaster([x[0] , "|" , x[2][0]]))
                        output.append("&")
                        output.append(removeDistributionMaster([x[0], "|" , x[2][2]]))
                else:
                    output.append(removeDistributionMaster([x[0], "|", x[2][0]]))
                    output.append("&")
                    output.append(removeDistributionMaster([x[0], "|", x[2][2]]))
        else:
            output.append(x)
    return output












    # if checkToResolve == True:
    #     if firstIsList == True and secondIsList == True:
    #         for tempIterator in firstIsList:
    #             for tempSubIterator in

    #
    # #3 cases
    # #Case 1: Both are a list of predicates
    # #Case 2: Both are a single predicate
    # #Case 3: Either of them is a predicate
    # #Case 1: one is a list and the other is a single predicate
    # if list ==  type(first) and str == type(second) and len(first) == 2:
    #     tempOfFirst = splitThePredicate(first[1])
    #     tempOfSecond = splitThePredicate(second)
    #     retCode,dictionary = unify(tempOfFirst[1],tempOfSecond[1])
    #     if retCode == True:
    #         copyOfFirst = replaceVariableInAPredicate(first,dictionary)
    #         copyOfSecond = replaceVariableInAPredicate(second,dictionary)
    #         newTempPredicateToWorkOn = []
    #
    # if list == type(first) and  list == type(second) and 3 == len(first) and 3 == len(second):
    #     for iterator in first:
    #         for subiterator in second:
    #             #Need to check if this can be unified
    #             #1) Check if we both the predicate names are the same
    #             #2) Check what all variables can be unified.
    #             tempOfFirst     = splitThePredicate(iterator)
    #             tempOfSecond    = splitThePredicate(subiterator)
    #             if tempOfFirst[0] == tempOfSecond[0]:
    #                 if (len(iterator) == 2 and type(subiterator) == str and iterator[0] == '~') or \
    #                         (len(subiterator) == 2 and type(iterator) == str and subiterator[0] == '~'):
    #                     retCode,dictionary = unify(tempOfFirst[1],tempOfSecond[1])
    #                     if retCode == True:
    #                         copyOfFirst     = replaceVariableInAPredicate(first,dictionary)
    #                         copyOfSecond    = replaceVariableInAPredicate(second,dictionary)
    #                         newTempPredicateToWorkOn = []
    #                         for newIterator in copyOfFirst:
    #                             if newIterator != '|' and newIterator != iterator and newIterator != subiterator:
    #                                 newTempPredicateToWorkOn.append(newIterator)
    #                                 newTempPredicateToWorkOn.append('|')
    #                         for newIterator in copyOfSecond:
    #                             if newIterator != '|' and newIterator != iterator and newIterator != subiterator:
    #                                 newTempPredicateToWorkOn.append(newIterator)
    #                                 newTempPredicateToWorkOn.append('|')
    #             newPredicate.append(newTempPredicateToWorkOn[:len(newTempPredicateToWorkOn-1)])
    # elif str == type(first) and str == type(second):
    #     return False
    # elif str == type(first) and list == type(second) and 2 == len(second):
    #     #Check if this can be unified
    #     tempOfFirst     = splitThePredicate(first)
    #     tempOfSecond    = splitThePredicate(second[1])
    #     if tempOfFirst[0] == tempOfSecond[0]:
    #         retCode,dictionary = unify(tempOfFirst[1],tempOfSecond[1])
    #         if retCode == True:
    #             #Both can be unified
    #             return None
    #         else:
    #             return False
    #     else:
    #         return False
    # elif str == type(second) and list == type(first) and 2 == len(first):
    #         # Check if this can be unified
    #         tempOfFirst = splitThePredicate(second)
    #         tempOfSecond = splitThePredicate(first[1])
    #         if tempOfFirst[0] == tempOfSecond[0]:
    #             retCode, dictionary = unify(tempOfFirst[1], tempOfSecond[1])
    #             if retCode == True:
    #                 # Both can be unified
    #                 return None
    #             else:
    #                 return False
    #         else:
    #             return False

    #     else:
    #         return False
    # elif str == type(first) or (2 == len(first) and list == type(first))\
    #     and str == type(second) or (2 == len(second) and list == type(second)):
    #     #Cases to handle
    #     #Check if this can be unified
    #     #If yes unify
    #     #Detect which among this is a single predicate
    # return newPredicate


for iterator in range(0, len(newPairsToCheck)):
    resolve.append(resolveFurther(newPairsToCheck[iterator][0], newPairsToCheck[iterator][1]))

for res in resolve:
    if len(res) > 0:
        if res not in KBListToActOn:
            superCounter += 1


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

                    retCode,dictionary = unify(tempSplitOne[1],tempSplitTwo[1],dictionary)
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
                retCode,dictionary = unify(tempSplitOne[1],tempSplitTwo[1],dictionary)
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
                retCode,dictionary = unify(tempSplitOne[1],tempSplitTwo[1],dictionary)
    else:
        if len(firstToCheck) == 2 and type(firstToCheck) == list:
            tempSplitOne = splitThePredicate(firstToCheck[1])
        elif type(firstToCheck) == str:
            tempSplitOne = splitThePredicate(firstToCheck)
        if len(secondToCheck) == 2 and type(secondToCheck) == list:
            tempSplitTwo = splitThePredicate(secondToCheck[1])
        elif type(secondToCheck) == str:
            tempSplitTwo = splitThePredicate(secondToCheck)
        retCode, dictionary = unify(tempSplitOne[1], tempSplitTwo[1], dictionary)
    return dictionary
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
    while True:
        lengthOfTheKB = len(KBListToActOn)
        newPairsToCheck = []
        superCounter = 0
        for iterator in range(0,lengthOfTheKB):
            for subiterator in range(iterator+1,lengthOfTheKB):
                newPairsToCheck.append((KBListToActOn[iterator],KBListToActOn[subiterator]))
        resolve = []
        #Resolve
        for iterator in range(0,len(newPairsToCheck)):
            count += 1
            # print "unifying " +  str(newPairsToCheck[iterator][0]) + " and " + str(newPairsToCheck[iterator][1])
            answer = resolveFurtherBruteForceOrignalVersionOne(newPairsToCheck[iterator][0], newPairsToCheck[iterator][1])
            # answer = answer[0] if len(answer) > 0 else answer
            answer = answer[0] if type(answer) == list and len(answer) == 2 and ((type(answer[0]) == str)\
                                    or\
                                  (type(answer[0]) == list and len(answer[0]) == 2  and type(answer[0][1]) == str)) else answer
            answer = answer[0] if type(answer) == list and len(answer) == 1 else answer
            if answer not in KBListToActOn and len(answer) > 0:
                superCounter +=1
                # answer = standarizeKB(answer)
                KBListToActOn.append(answer)
                # print "Answer " + str(answer)

            #Check the facts
            if type(answer) == str :
                variablesOfAnswer = splitThePredicate(answer)
                isFact = True
                for superAnswerIterator in variablesOfAnswer[1]:
                    if superAnswerIterator[0].islower() == True:
                        isFact = False
                        break
                if isFact == True and ['~',answer] in KBListToActOn:
                    return True
            if type(answer) == list and len(answer) == 2 and answer[0] == '~' and type(answer[1]) == str  :
                variablesOfAnswer = splitThePredicate(answer[1])
                isFact = True
                for superAnswerIterator in variablesOfAnswer[1]:
                    if superAnswerIterator[0].islower() == True:
                        isFact = False
                        break
                if isFact == True and answer[1] in KBListToActOn:
                    return True


        if superCounter == 0:
            return False