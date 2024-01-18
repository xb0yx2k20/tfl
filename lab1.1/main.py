from lab1 import main

lines = []
with open("input.txt", "r") as file:
    str = file.readlines()

for s in str:
    lines.append(s)

rules = []
for i in lines:
    #count_funcs(i)
    i = i.replace('\n', '')
    rules.append(i.split(' -> '))

#print(rules)
main(rules, 'g(g(t, t), g(t, t))', 1)