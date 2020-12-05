import os
import re

head=[">> Loss", ">> More"]

def parse(lines, t=0):
    res = {}
    for line in lines:
        if "//" in line and ":" in line or t:
            if t:
                line = line.replace("\n", "")
            else:
                line = line.split(" ", 1)[1].replace("\n", "")
            sline = re.split("[:, ]", line)
            res[sline[0]] = []
            for f in sline[1:]:
                if f:
                    res[sline[0]].append(f)
    return res

def p(ans, res, t=0):
    for num in ans:
        if num not in res:
            print("{} {}: {}".format(head[t], num, ans[num]))
            continue
        err = 0
        for f in ans[num]:
            if f not in res[num]:
                if not err:
                    print("{} {}: ".format(head[t], num), end="")
                    err = 1
                print(" {}".format(f), end="")
        if err:
            print()


for i in range(35):
    testc = "test/test{:0>2d}.c".format(i)
    testc = open(testc, "r")
    print(">>>>> test {:0>2d}".format(i))
    ans = parse(testc.readlines())
    testc.close()
    testll = "testll/test{:0>2d}.ll".format(i)
    os.system("./assignment3 {} 2>tmp.txt".format(testll))
    tmp = open("tmp.txt", "r")
    res = parse(tmp.readlines(), 1)
    tmp.close()
    p(ans, res, 0)
    p(res, ans, 1)
    print()


