def UNIFY_VAR(var, x, theta):
    if var in theta.keys():
        return UNIFY(theta[var], x, theta)
    elif x in theta.keys():
        return UNIFY(var, theta[x], theta)
    else:
        if var[0].islower():
            theta[var] = x
        elif x[0].islower():
            theta[x] = var
        else:
            theta[var] = x
    return theta


def UNIFY(X,Y,theta):
    if  theta == False:
        return False
    elif X == Y:
        return theta
    elif type(X) is not list and X[0].islower():
        return UNIFY_VAR(X,Y,theta)
    elif type(Y) is not list and Y[0].islower():
        return UNIFY_VAR(Y, X, theta)
    elif type(X) is list and type(Y) is list:
        return UNIFY(X[1:], Y[1:], UNIFY(X[0], Y[0], theta))
    else:
        return False

pred1 = "Ankur(x,y)" #Split this to just x and y and put it in a list
pred2 = "Ankur(Jhon,y)" #Split this to Jhon and Y and put it in a list

test1 = ['x','y']
test2 = ['Jhon','y']

print UNIFY(test1,test2,{})