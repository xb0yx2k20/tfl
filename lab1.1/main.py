from TRS import TRSRule


def main():
    with open('input.txt', 'r') as input_file, open('output.txt', 'w') as output_file:
        n_equals_line = input_file.readline()
        n = int(n_equals_line[4:]) 

        print("n =", n)
        
        input_file.read(12) 
        variables = set()
        variables.add(input_file.read(1))

        while input_file.read(1) == ',':
            variables.add(input_file.read(1))

        print("variables =", variables)

        input_file.read(8) 
        start = TRSRule.Term.from_file(input_file, variables)
        
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

        for rule in trs:
            print(rule)
        print()

        rewritten_terms = []
        rewritten_terms = start.rewrite(rewritten_terms, trs, n)


        for term in rewritten_terms:
            output_file.write(str(term))
            output_file.write('\n')
            
            print(term)

if __name__ == "__main__":
    main()
