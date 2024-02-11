from typing import TextIO
import copy



class TRSRule:
    class Term:
        def __init__(self, n_constructor, n_parameters, n_is_variable):
            self.n_constructor = n_constructor
            self.n_parameters = n_parameters
            self.n_is_variable = n_is_variable

        @classmethod
        def from_file(cls, input: TextIO, variables: set):
            term = cls(input.read(1), [], False)

            if term.n_constructor in variables:
                term.n_is_variable = True
                return term

            if input.read(1) != '(': # )
                input.seek(input.tell() - 1)
                return term

            term.n_parameters.append(TRSRule.Term.from_file(input, variables))
            while input.read(1) == ',':
                term.n_parameters.append(TRSRule.Term.from_file(input, variables))

            return term

        def __str__(self):
            result = str(self.n_constructor)
            if len(self.n_parameters) != 0:
                result += '(' # )
                for i in range(len(self.n_parameters)):
                    result += self.n_parameters[i].__str__()
                    if (i + 1 != len(self.n_parameters)):
                        result += ','
                result += ')'
            return result

        def is_equal(self, term):
            reflex = dict()
            return self._is_equal(term, reflex), reflex

        def interpret_with(self, term) -> dict:
            reflex = dict()
            reflex = self._interpret_with(term, reflex)
            return reflex

        def apply_reflex(self, reflex: dict):
            if self.n_is_variable:
                if self.n_constructor in reflex:
                    return copy.deepcopy(reflex[self.n_constructor])

                return copy.deepcopy(self)

            result_term = copy.deepcopy(self)

            for i in range(len(result_term.n_parameters)):
                result_term.n_parameters[i] = result_term.n_parameters[i].apply_reflex(reflex)

            return result_term

        def rewrite(self, results: list, trs: list, n) -> list:
            if n == 0:
                results.append(self)
                return results

            if self.n_is_variable:
                return results

            # развертка конструктора
            # for rule in trs:
            for i in range(len(trs)):
                reflex = trs[i].left_term.interpret_with(self)
                if not reflex:
                    continue

                term_rewrite = trs[i].right_term.apply_reflex(reflex)
                results = term_rewrite.rewrite(results, trs, n - 1)

            # развертки агрументов конструктора
            for i in range(len(self.n_parameters)):
                # копируем подтерм
                subterm = copy.deepcopy(self)
                subresults = []

                # рекурсивно переписываем
                subresults = subterm.n_parameters[i].rewrite(subresults, trs, n)

                # подставляем переписанный терм на место
                for rewrited_term in subresults:
                    subterm.n_parameters[i] = copy.deepcopy(rewrited_term)
                    results.append(copy.deepcopy(subterm))
            return results

        def _interpret_with(self, term, inp_reflex: dict) -> dict:
            reflex = copy.deepcopy(inp_reflex)
            # случай сравнения переменной с термом
            if self.n_is_variable:
                # если переменная уже имеет отображение, сравниваем
                if self.n_constructor in reflex:
                    comp = reflex[self.n_constructor].is_equal(term)
                    if not comp[1]:
                        reflex.clear()
                    return reflex

                # добавляем новое отображение переменной
                reflex[self.n_constructor] = term
                return reflex

            # если неравны конструкторы или количество параметров, то и термы неравны
            if self.n_constructor != term.n_constructor or len(self.n_parameters) != len(term.n_parameters):
                reflex.clear()
                return reflex

            for i in range(len(self.n_parameters)):
                new_reflex = self.n_parameters[i]._interpret_with(term.n_parameters[i], reflex);
                if not new_reflex:
                    return new_reflex
                else:
                    reflex.update(new_reflex)
                # reflex.update(self.n_parameters[i]._interpret_with(term.n_parameters[i], reflex));
                # if not reflex:
                #     return reflex

            return reflex

        def _is_equal(self, term, reflex: dict):
            # если термы не одного типа они не равны
            if self.n_is_variable != term.n_is_variable:
                return False, reflex

            if self.n_is_variable:
                if self.n_constructor in reflex:
                    return reflex[self.n_constructor] == term.n_constructor, reflex

                reflex[self.n_constructor] = copy.deepcopy(term.n_constructor)
                return True, reflex

            if self.n_constructor != term.n_constructor or len(self.n_parameters) != len(term.n_parameters):
                return False, reflex

            for i in range(len(self.n_parameters)):
                comp, reflex = self.n_parameters[i]._is_equal(term.n_parameters[i], reflex)
                if not comp:
                    return False, reflex
            return True, reflex

    def __init__(self, left_term, right_term):
        self.left_term = left_term
        self.right_term = right_term

    def __str__(self):
        return f"{self.left_term.__str__()} = {self.right_term.__str__()}"


