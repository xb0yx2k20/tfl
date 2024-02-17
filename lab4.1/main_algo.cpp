#include <utility>

#include "automat.cpp"

struct Rule {
    std::string left;
    std::vector <std::string> right;
};

std::vector<std::string> split(std::string s, std::string delimiter) {
    size_t pos_start = 0, pos_end, delim_len = delimiter.length();
    std::string token;
    std::vector<std::string> res;

    while ((pos_end = s.find(delimiter, pos_start)) != std::string::npos) {
        token = s.substr (pos_start, pos_end - pos_start);
        pos_start = pos_end + delim_len;
        res.push_back (token);
    }

    res.push_back (s.substr (pos_start));
    return res;
}

void showRule(const Rule& r) {
    std::cout << r.left << " -> ";
    for (auto s : r.right) {
        std::cout << s << " ";
    }
    std::cout << std::endl;
}

std::vector <char> getNonterminals(const Rule& r) {
    std::vector <char> res;
    for (auto s : r.right) {
        if (s.size() == 1 && isupper(s[0])) {
            res.push_back(s[0]);
        }
    }
    return res;
}

void deleteNonGenerativeRules(std::vector <Rule>& G) {
    std::set <char> generative_rules;
    for (auto rule : G) {
        if (getNonterminals(rule).empty()) {
            generative_rules.insert(rule.left[0]);
        }
    }

    while(1) {
        bool end_f = true;
        for (auto rule : G) {
            std::vector <char> nonterms = getNonterminals(rule);
            int f = 0;
            for (auto term : nonterms) {
                if (!generative_rules.count(term)){
                    f = 1;
                    break;
                }
            }
            if (f == 0 && !generative_rules.count(rule.left[0])) {
                end_f = false;
                generative_rules.insert(rule.left[0]);
            }
        }
        if (end_f) break;
    }

    for (int i = 0; i < G.size(); i++) {
        if (!generative_rules.count(G[i].left[0])) {
            G.erase(G.begin() + i);
            i--;
            continue;
        }
        std::vector <char> nonterms = getNonterminals(G[i]);
        for (auto term : nonterms) {
            if (!generative_rules.count(term)) {
                G.erase(G.begin() + i);
                i--;
                break;
            }
        }
    }
}

void deleteNonAchievableRules(std::vector <Rule>& G) {
    std::set <char> reachable_terms;
    reachable_terms.insert('S');
    int set_size = reachable_terms.size();
    while(1) {
        for (auto rule : G) {
            if (reachable_terms.count(rule.left[0])) {
                std::vector <char> nonterms = getNonterminals(rule);
                for (auto term : nonterms) {
                    reachable_terms.insert(term);
                }
            }
        }
        if (reachable_terms.size() > set_size) {
            set_size = reachable_terms.size();
        }
        else break;
    }

    for (int i = 0; i < G.size(); i++) {
        if (!reachable_terms.count(G[i].left[0])) {
            G.erase(G.begin() + i);
            i--;
            continue;
        }
        std::vector <char> nonterms = getNonterminals(G[i]);
        for (auto term : nonterms) {
            if (!reachable_terms.count(term)) {
                G.erase(G.begin() + i);
                i--;
                break;
            }
        }
    }
}

std::vector<std::pair<std::pair<int, int>, std::string>> get_transitions(automaton a){
    std::vector<std::pair<std::pair<int, int>, std::string>> res;
    auto matrix = a.get_transition_matrix();
    for (int i = 0; i < matrix.size(); i++){
        for (int j = 0; j < matrix.size(); j++){
            if (matrix[i][j].first != "0"){
                res.emplace_back(std::pair<int,int>(i, j), matrix[i][j].first);
            }
        }
    }
    return res;
}

std::vector<std::pair<std::pair<std::pair<int, std::string>, int>, std::string>> get_term_rules(std::vector<std::pair<std::pair<int, int>, std::string>> transitions, std::vector<Rule> rules, automaton a){
    std::vector<std::pair<std::pair<std::pair<int, std::string>, int>, std::string>> res;
    for (auto & rule : rules){
        if (rule.right.size() == 1){
            for (auto & transition : transitions){
                if (rule.left == "S" && (a.get_start_states()[transition.first.first] != 1 || a.get_end_states()[transition.first.second] != 1)){
                    continue;
                }
                if (rule.right[0].size() == 1){
                    if (rule.right[0] == transition.second){
                        res.push_back({{{transition.first.first, rule.left}, transition.first.second}, transition.second});
                    }
                } else if (rule.right[0].size() > 1) {
                    auto splitted_str = split(rule.right[0], "|");
                    for (const auto & z : splitted_str){
                        if (z == transition.second){
                            res.push_back({{{transition.first.first, rule.left}, transition.first.second}, transition.second});
                        }
                    }
                }
            }
        }
    }
    return res;
}

std::vector<Rule> main_algo(automaton a, std::vector<Rule> g){
    std::vector<Rule> res;
    auto transitions = get_transitions(a);
    auto term_rules = get_term_rules(transitions, g, a);

    std::vector<std::pair<std::pair<std::pair<std::pair<int, std::string>, int>, std::string>, bool>> new_term_rules;
    for (auto & term_rule : term_rules){
        new_term_rules.emplace_back(term_rule, false);
    }
//    for (auto e : new_term_rules){
//        std::cout << e.first.first.first.first << " " << e.first.first.first.second << " " << e.first.first.second << " " << e.first.second << " " << e.second << std::endl;
//    }
    while (true){
        bool flag = false;
        for (auto & i : g){
            if (i.right.size() > 1){
                for (int j = 0; j < new_term_rules.size(); j++){
                    for (int k = 0; k < new_term_rules.size(); k++){
                        if (j != k && new_term_rules[j].first.first.second == new_term_rules[k].first.first.first.first && new_term_rules[j].first.first.first.second == i.right[0] && new_term_rules[k].first.first.first.second == i.right[1]){
                            if (i.left == "S" && (a.get_start_states()[new_term_rules[j].first.first.first.first] != 1 || a.get_end_states()[new_term_rules[k].first.first.second] != 1)){
                                continue;
                            }
                            bool rule_flag = false;
                            for (auto & re : res){
                                if (re.left == i.left && re.right == i.right){
                                    rule_flag = true;
                                }
                            }
                            new_term_rules.push_back({{{{new_term_rules[j].first.first.first.first, i.left}, new_term_rules[k].first.first.second}, "!"}, false});
                            new_term_rules[j].second = true;
                            new_term_rules[k].second = true;
                            if (!rule_flag){
                                res.push_back(i);
//                                for (auto e : new_term_rules){
//                                    std::cout << e.first.first.first.first << " " << e.first.first.first.second << " " << e.first.first.second << " " << e.first.second << " " << e.second << std::endl;
//                                }
                                flag = true;
                            }
                        }
                    }
                }
            }
        }
        if (!(flag)){
            break;
        }
    }

//    std::cout << "========" << std::endl;
//    for (auto r : res){
//        showRule(r);
//    }
//    std::cout << "========" << std::endl;

    for (auto & new_term_rule : new_term_rules){
        if (new_term_rule.second){
            std::string left = new_term_rule.first.first.first.second;
            std::vector<std::string> right = {new_term_rule.first.second};
            bool rule_flag = false;
            for (auto & re : res){
                if (re.left == left && re.right == right){
                    rule_flag = true;
                }
            }
            if (!rule_flag){
                res.push_back({left, right});
            }
        }
    }

    for (int i = 0; i < res.size(); i++){
        if (res[i].right.empty() || res[i].right[0] == "!"){
            res.erase(res.begin() + i);
        }
    }
//    for (auto r : res){
//        showRule(r);
//    }
    return res;
}