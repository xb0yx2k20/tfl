from TRS import TRSRule


def main():
    CONSOLE_LOG = True
    with open('input.txt', 'r') as input_file, open('output.txt', 'w') as output_file:
        n_equals_line = input_file.readline()
        n = int(n_equals_line[4:]) 

        if CONSOLE_LOG:
            print("n =", n)
        
        input_file.read(12) 
        variables = set()
        variables.add(input_file.read(1))

        while input_file.read(1) == ',':
            variables.add(input_file.read(1))

        if CONSOLE_LOG:
            print("variables =", variables)

        input_file.read(8) 
        start = TRSRule.Term.from_file(input_file, variables)
        
        if CONSOLE_LOG:
            print("start =", start)

        trs = []
        input_file.read(1)
        read_sym = input_file.read(1)
        while (read_sym != '' and read_sym != ' ' and read_sym != '\n'):
            input_file.seek(input_file.tell() - 1)
            left_term = TRSRule.Term.from_file(input_file, variables)
            input_file.read(3) 
            right_term = TRSRule.Term.from_file(input_file, variables)
            trs.append(TRSRule(left_term, right_term))
            input_file.read(1)
            read_sym = input_file.read(1)

        if CONSOLE_LOG:
            for rule in trs:
                print(rule)
        
        rewritten_terms = []
        rewritten_terms = start.rewrite(rewritten_terms, trs, n)

        if CONSOLE_LOG:
            print()

        for term in rewritten_terms:
            output_file.write(str(term))
            output_file.write('\n')
            
            if CONSOLE_LOG:
                print(term)

if __name__ == "__main__":
    main()
