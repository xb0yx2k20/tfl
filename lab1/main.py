import sys
import subprocess
import os
import lab1

def fix(decl):
    fixic = []
    for i in decl:
        for j in i:
            if j not in fixic:
                fixic.append(j)
    res = ''
    for x in fixic:
        res += x
    return res


lines = ''
with open("input.txt", "r") as file:
    str = file.readlines()
    
decl = []
accert = ''
for s in str:
    data = lab1.main(s.replace('\n', ''))
    decl.append(data[0])
    accert += data[1]


declare = fix(decl)
message = (declare + accert)
message += '''(check-sat)
(get-model)
(exit)'''

f = open("lab1.smt2", "w")

f.write(message)
f.close()

proc = subprocess.Popen("z3 -smt2 lab1.smt2", stdout=subprocess.PIPE, shell=True)
(out, err) = proc.communicate()

result = out.decode()

        
with open("output.txt", "w") as f:
    f.write(result)
print("Результат записан в output.txt")

os.remove("lab1.smt2")
