dict = {}

dict['a'] = 'b'
dict['b'] = 'c'
dict['c'] = 'g'
dict['e'] = 'F'

key = 'a'
value = dict[key]

while value in dict:
    key = value
    value = dict[key]

print key,value

