#include <iostream>
#include <fstream>
#include <vector>
#include <sstream>
#include <cassert>
#include <set>
#include <map>
#include <utility>
#include <stack>
#include <algorithm>

const std::string CONCAT_OP = "·";
const std::string INTERSECT_OP = "∩";

class automaton {
private:
    std::vector<int> start_states;
    std::vector<std::vector<std::pair<std::string, bool>>> transition_matrix;
    std::vector<int> end_states;

    std::vector <bool> visited;
public:
    automaton() = default;
    std::vector<int> get_start_states();
    std::vector <std::vector <std::pair<std::string, bool>>> get_transition_matrix();
    std::vector<int> get_end_states();
    std::vector<bool> get_visited();
    void dfs(int vertex);
    void dfs_from_starts();
    void print_start_vector();
    void print_transition_matrix();
    void print_end_vector();
    void show_automaton();
    void show_like_arrows();
    void dfs_transpon(int vertex);
    automaton get_addition_automaton();

    automaton(std::vector<int> p_start_states,
              std::vector<std::vector<std::pair<std::string, bool>>> p_transition_matrix,
              std::vector<int> p_end_states);
    automaton(std::vector<int> p_start_states,
              std::vector<std::vector<std::pair<std::string, bool>>> p_transition_matrix,
              std::vector<int> p_end_states,
              std::vector<bool> p_visited);
};

void automaton::print_start_vector() {
    for (int start_state : start_states){
        std::cout << start_state << " ";
    }
    std::cout << std::endl;
}

void automaton::print_transition_matrix() {
    for (auto & i : transition_matrix){
        for (const auto & j : i){
            std::cout << j.first << " ";
        }
        std::cout << std::endl;
    }
}

void automaton::print_end_vector() {
    for (int end_state : end_states){
        std::cout << end_state << std::endl;
    }
}

void automaton::show_automaton() {
    this->print_start_vector();
    std::cout << std::endl;
    this->print_transition_matrix();
    std::cout << std::endl;
    this->print_end_vector();
    std::cout << std::endl;
}

struct TreeNode {
    std::pair<std::string, std::string> data;
    struct TreeNode *left{};
    struct TreeNode *right{};

    TreeNode(){
        this->data = {"",""};
        this->left = nullptr;
        this->right = nullptr;
    }

    TreeNode(const std::pair<std::string, std::string> &data, TreeNode *left, TreeNode *right) {
        this->data = data;
        this->left = left;
        this->right = right;
    }
};

TreeNode* build_tree(const std::vector <std::pair <std::string, std::string > >& postfix) {
    if (postfix.empty()) return nullptr;

    std::stack <TreeNode*> s;
    int c = 1;

    for (const auto& elem : postfix) {
        if (elem.second != "TERM") {
            TreeNode *x = s.top();
            TreeNode *y;
            s.pop();
            if (elem.second == "UNARY"){
                auto* node = new TreeNode(elem, x, nullptr);
                s.push(node);
            }
            else{
                y = s.top();
                s.pop();
                auto* node = new TreeNode(elem, y, x);
                s.push(node);
            }
        }
        else {
            s.push(new TreeNode({elem.first + std::to_string(c), elem.second}, nullptr, nullptr));
            c++;
        }
    }
    return s.top();
}


class FFL {
public:
    std::set<std::string> First{};
    std::map<std::string, std::set<std::string> > Follow{};
    std::set<std::string> Last{};
    int flag = 0;

    FFL() = default;

    explicit FFL(const std::pair<std::string, std::string> &term) {
        assert(term.second == "TERM");
        First.insert(term.first);
        Last.insert(term.first);
        Follow[term.first] = {};
    }

    void show() {
        std::cout << "First: {";
        for (const auto &elem: this->First) {
            std::cout << elem << " ";
        }
        std::cout << "}\n";

        std::cout << "Last: {";
        for (const auto &elem: this->Last) {
            std::cout << elem << " ";
        }
        std::cout << "}\n";

        for (const auto &elem: this->Follow) {
            std::cout << "Follow(" << elem.first << ") = {";
            for (const auto &i: elem.second) {
                std::cout << i << " ";
            }
            std::cout << "}\n";
        }
        std::cout << std::endl;
        std::cout << "Empty word accept: " << this->flag << std::endl;
    }
    void concatenate(const FFL& b){
        for (const auto& elem : this->Last){
            this->Follow[elem].insert(b.First.begin(), b.First.end());
        }

        for (const auto& elem : b.Follow) {
            this->Follow[elem.first] = elem.second;
        }

        if (!b.flag){  // НЕ примнимает пустое слово
            this->Last = b.Last;
            if (this->flag) {
                this->First.insert(b.First.begin(), b.First.end());
            }
        }
        else{
            this->Last.insert(b.Last.begin(), b.Last.end());
            if (this->flag){
                this->First.insert(b.First.begin(), b.First.end());
            }
        }
        if (!b.flag){
            this->flag = 0;
        }
    }

    void alternative(const FFL& b){
        for (const auto& elem : b.Follow) {
            this->Follow[elem.first] = elem.second;
        }
        this->First.insert(b.First.begin(), b.First.end());
        this->Last.insert(b.Last.begin(), b.Last.end());
        this->flag = this->flag || b.flag;
    }

    void unary(){
        this->flag = true;
        for (const auto& elem : this->Last){
            this->Follow[elem].insert(this->First.begin(), this->First.end());
        }
    }

    int get_states_count(){
        std::set <std::string> buf;
        std::set <std::string>::iterator iter;
        std::map <std::string, std::set <std::string> >::iterator it;
        for (it = this->Follow.begin(); it != this->Follow.end(); it++){
            buf.insert(it->first);
        }
        return buf.size() + 1; // +1 because of start state exists
    }

    int check_state_number(const std::string& state){
        std::map <std::string, std::set <std::string> >::iterator it;
        int cnt = 1;
        for (it = this->Follow.begin(); it != this->Follow.end(); it++){
            if (state == it->first){
                return cnt;
            }
            cnt += 1;
        }
        return 0;
    }

    automaton ffl_2_glushkov(){
        int states_number = get_states_count();
        std::vector<int> start_states(states_number, 0);
        start_states[0] = 1;

        std::vector<std::vector<std::pair<std::string, bool>>> transition_matrix(states_number, std::vector<std::pair<std::string, bool>>(states_number, {"0", false}));
        for (int i = 0; i < this->First.size(); i++){
            auto state = this->First.begin();
            for(int j=0;j<i;j++){
                state++;
            }
            int index = check_state_number(*state);
            transition_matrix[0][index].first = *state;
        }

        std::map <std::string, std::set <std::string> >::iterator it;
        for (it = this->Follow.begin(); it != this->Follow.end(); it++){
            int i = check_state_number(it->first);
            for (int ind = 0; ind < it->second.size(); ind++){
                auto transit_to = it->second.begin();
                for (int z = 0; z < ind; z++){
                    transit_to++;
                }
                int j = check_state_number(*transit_to);
                transition_matrix[i][j].first = *transit_to;
            }
        }

        std::vector<int> end_states(get_states_count(), 0);
        if (this->flag){
            end_states[0] = 1;
        } else {
            std::set<std::string>::iterator ite;
            for (ite = this->Last.begin(); ite != this->Last.end(); ite++){
                end_states[check_state_number(*ite)] = 1;
            }
        }
        for (int i = 0; i < transition_matrix.size(); i++){
            for (int j = 0; j < transition_matrix.size(); j++){
                if (transition_matrix[i][j].first != "0"){
                    std::string::iterator end_pos = std::remove_if(transition_matrix[i][j].first.begin(), transition_matrix[i][j].first.end(),
                                                                   isdigit);
                    transition_matrix[i][j].first.erase(end_pos, transition_matrix[i][j].first.end());
                }
            }
        }
        return {start_states, transition_matrix, end_states};
    }
};

automaton::automaton(std::vector <int> p_start_states, std::vector <std::vector <std::pair<std::string, bool>>> p_transition_matrix, std::vector <int> p_end_states) {
    start_states = std::move(p_start_states);
    transition_matrix = std::move(p_transition_matrix);
    end_states = std::move(p_end_states);
    visited = std::vector<bool>(start_states.size(), false);
}
automaton::automaton(std::vector <int> p_start_states, std::vector <std::vector <std::pair<std::string, bool>>> p_transition_matrix, std::vector <int> p_end_states, std::vector<bool> p_visited) {
    start_states = std::move(p_start_states);
    transition_matrix = std::move(p_transition_matrix);
    end_states = std::move(p_end_states);
    visited = std::move(p_visited);
}

std::vector<int> automaton::get_start_states() {
    return start_states;
}

void automaton::show_like_arrows() {
    std::cout << "digraph G {" << std::endl;
    std::cout << "rankdir=\"LR\";" << std::endl;
    for (int i = 0; i < this->transition_matrix.size(); i++){
        for (int j = 0; j < this->transition_matrix.size(); j++){
            if (this->transition_matrix[i][j].first != "0"){
                std::cout << std::to_string(i) << " -> " << std::to_string(j) << " [label=\"" << this->transition_matrix[i][j].first << "\"];" << std::endl;
            }
        }
    }
    for (int i = 0; i < this->end_states.size(); i++){
        if (this->end_states[i]){
            std::cout << std::to_string(i) <<  " [label=\"" << std::to_string(i) << "\", shape=doublecircle];" << std::endl;
        } else {
            std::cout << std::to_string(i) <<  " [label=\"" << std::to_string(i) << "\", shape=circle];" << std::endl;
        }
    }
    std::cout << "}" << std::endl;
}

std::vector <std::vector <std::pair<std::string, bool>>> automaton::get_transition_matrix(){
    return transition_matrix;
}

std::vector<int> automaton::get_end_states(){
    return end_states;
}

void automaton::dfs(int vertex){
    this->visited[vertex] = true;
    for (int j = 0; j < this->transition_matrix[vertex].size(); j++){
        if (this->transition_matrix[vertex][j].first != "0" && !this->visited[j]){
            dfs(j);
        }
    }
}

void automaton::dfs_from_starts() {
    for (int i = 0; i < this->start_states.size(); i++){
        if (this->start_states[i]){
            dfs(i);
        }
    }
}

std::vector<bool> automaton::get_visited() {
    return this->visited;
}

FFL process_tree(TreeNode* node){
    if (node->data.second == "UNARY") {
        auto a = process_tree(node->left);
        a.unary();
        return a;
    }
    if (node->data.first == CONCAT_OP){
        auto a = process_tree(node->left);
        auto b = process_tree(node->right);
        a.concatenate(b);
        return a;
    }
    if (node->data.first == "|"){
        auto a = process_tree(node->left);
        auto b = process_tree(node->right);
        a.alternative(b);
        return a;
    }
    return FFL(node->data);
}

automaton iteration_automaton(automaton& auto1){
    if (auto1.get_transition_matrix().empty()){
        return {std::vector<int>(1, 1), std::vector <std::vector <std::pair<std::string, bool>>>(1, std::vector<std::pair<std::string, bool>>(1, {"0", false})), std::vector<int>(1, 1)};
    }
    std::vector<int> start_states = auto1.get_start_states();

    std::vector<int> end_states = auto1.get_end_states();
    end_states[0] = 1;

    std::vector <std::vector <std::pair<std::string, bool>>> transition_matrix (auto1.get_transition_matrix().size(), std::vector<std::pair<std::string, bool>>(auto1.get_transition_matrix().size(), {"0", false}));
    for (int j = 1; j < auto1.get_transition_matrix().size(); j++){
        transition_matrix[0][j].first = auto1.get_transition_matrix()[0][j].first;
    }
    for (int i = 1; i < auto1.get_transition_matrix().size(); i++){
        for (int j = 1; j < auto1.get_transition_matrix().size(); j++){
            if (end_states[i]){
                if (transition_matrix[0][j].first == "0"){
                    transition_matrix[i][j].first = auto1.get_transition_matrix()[i][j].first;
                } else if (auto1.get_transition_matrix()[i][j].first == "0"){
                    transition_matrix[i][j].first = transition_matrix[0][j].first;
                } else {
                    if (transition_matrix[0][j].first != auto1.get_transition_matrix()[i][j].first){
                        transition_matrix[i][j].first = "(" + transition_matrix[0][j].first + "|" + auto1.get_transition_matrix()[i][j].first + ")";
                    } else {
                        transition_matrix[i][j].first = transition_matrix[0][j].first;
                    }
                }
            } else {
                transition_matrix[i][j].first = auto1.get_transition_matrix()[i][j].first;
            }
        }
    }
    return {start_states, transition_matrix, end_states};
}

automaton intersect_automatons(automaton& auto1, automaton& auto2){
    std::vector<int> start_states(auto1.get_start_states().size() * auto2.get_start_states().size(), 0);
    for (int i = 0; i < auto1.get_start_states().size(); i++){
        for (int j = 0; j < auto2.get_start_states().size(); j++){
            if (auto1.get_start_states()[i] && auto2.get_start_states()[j]){
                start_states[i * auto2.get_end_states().size() + j] = 1;
            }
        }
    }

    std::vector<int> end_states(auto1.get_end_states().size() * auto2.get_end_states().size(), 0);
    for (int i = 0; i < auto1.get_end_states().size(); i++){
        for (int j = 0; j < auto2.get_end_states().size(); j++){
            if (auto1.get_end_states()[i] && auto2.get_end_states()[j]){
                end_states[i * auto2.get_end_states().size() + j] = 1;
            }
        }
    }

    std::vector <std::vector <std::pair<std::string, bool>>> transition_matrix(auto1.get_transition_matrix().size() * auto2.get_transition_matrix().size(), std::vector <std::pair<std::string, bool>> (auto1.get_transition_matrix().size() * auto2.get_transition_matrix().size(), {"0",
                                                                                                                                                                                                                                                                                      false})) ;
    for (int i = 0; i < auto1.get_transition_matrix().size(); i++){
        for (int j = 0; j < auto1.get_transition_matrix()[i].size(); j++){
            for (int k = 0; k < auto2.get_transition_matrix().size(); k++){
                for (int z = 0; z < auto2.get_transition_matrix()[k].size(); z++){
                    if (auto1.get_transition_matrix()[i][j] == auto2.get_transition_matrix()[k][z] && auto1.get_transition_matrix()[i][j].first != "0"){
                        transition_matrix[i * auto2.get_transition_matrix().size() + k][j * auto2.get_transition_matrix().size() + z].first = auto1.get_transition_matrix()[i][j].first;
                    }
                }
            }
        }
    }

    automaton res(start_states, transition_matrix, end_states);
    res.dfs_from_starts();

    std::vector <bool> need_delete(transition_matrix.size(), false);
    for (int i = 0; i < transition_matrix.size(); i++){
        bool flag = true;
        for (int j = 0; j < transition_matrix.size(); j++){
            if (transition_matrix[i][j].first != "0" || transition_matrix[j][i].first != "0"){
                flag = false;
            }
        }
        need_delete[i] = flag;
    }
    for (int i = 0; i < res.get_visited().size(); i++){
        if (!res.get_visited()[i]){
            need_delete[i] = true;
        }
    }

    int cnt = 0;
    for (int i = 0; i < need_delete.size(); i++){
        if (need_delete[i]){
            start_states.erase(start_states.begin() + i - cnt);
            end_states.erase(end_states.begin() + i - cnt);
            transition_matrix.erase(transition_matrix.begin() + i - cnt);
            cnt += 1;
        }
    }
    cnt = 0;
    for (auto & i : transition_matrix){
        for (int j = 0; j < need_delete.size(); j++){
            if (need_delete[j]){
                i.erase(i.begin() + j - cnt);
                cnt += 1;
            }
        }
        cnt = 0;
    }
    for(int i = 0; i < res.get_visited().size(); i++){
        res.get_visited()[i] = false;
    }
    res = {start_states, transition_matrix, end_states};

    return res;
}

automaton alternative_automatons(automaton& auto1, automaton& auto2){
    if (auto1.get_transition_matrix().empty()){
        return auto2;
    } else if (auto2.get_transition_matrix().empty()){
        return auto1;
    }
    std::vector<int> start_states(auto1.get_start_states().size() + auto2.get_start_states().size() - 1, 0);
    for (int i = 0; i < auto1.get_start_states().size(); i++){
        if (auto1.get_start_states()[i]){
            start_states[i] = 1;
        }
    }
    for (int i = 1; i < auto2.get_start_states().size(); i++){
        if (auto2.get_start_states()[i]){
            start_states[auto1.get_start_states().size() + i - 1] = 1;
        }
    }

    std::vector <std::vector <std::pair<std::string, bool>>> transition_matrix (auto1.get_transition_matrix().size() + auto2.get_transition_matrix().size() - 1, std::vector<std::pair<std::string, bool>>(auto1.get_transition_matrix().size() + auto2.get_transition_matrix().size() - 1, {"0", false}));
    for (int i = 0; i < auto1.get_transition_matrix().size(); i++){
        for (int j = 0; j < auto1.get_transition_matrix().size(); j++){
            transition_matrix[i][j].first = auto1.get_transition_matrix()[i][j].first;
        }
    }
    for (int i = 0; i < auto2.get_transition_matrix().size(); i++){
        for (int j = 1; j < auto2.get_transition_matrix().size(); j++){
            if (i == 0){
                transition_matrix[i][auto1.get_transition_matrix().size() + j - 1].first = auto2.get_transition_matrix()[i][j].first;
            } else {
                transition_matrix[auto1.get_transition_matrix().size() + i - 1][auto1.get_transition_matrix().size() + j - 1].first = auto2.get_transition_matrix()[i][j].first;
            }
        }
    }

    std::vector<int> end_states (auto1.get_end_states().size() + auto2.get_end_states().size() - 1, 0);
    for (int i = 0; i < auto1.get_end_states().size(); i++){
        end_states[i] = auto1.get_end_states()[i];
    }
    for (int i = 0; i < auto2.get_end_states().size(); i++){
        if (i == 0){
            end_states[i] = end_states[i] || auto2.get_end_states()[i];
        } else {
            end_states[auto1.get_end_states().size() + i - 1] = auto2.get_end_states()[i];
        }
    }

    return {start_states, transition_matrix, end_states};
}

automaton concat_automatons(automaton& auto1, automaton& auto2){
    if (auto2.get_transition_matrix().empty()){
        return auto2;
    } else if (auto1.get_transition_matrix().empty()){
        return auto1;
    }
    std::vector<int> start_states(auto1.get_start_states().size() + auto2.get_start_states().size() - 1, 0);
    for (int i = 0; i < auto1.get_start_states().size(); i++){
        if (auto1.get_start_states()[i]){
            start_states[i] = 1;
        }
    }
    for (int i = 1; i < auto2.get_start_states().size(); i++){
        if (auto2.get_start_states()[i]){
            start_states[auto1.get_start_states().size() + i - 1] = 1;
        }
    }

    std::vector <std::vector <std::pair<std::string, bool>>> transition_matrix (auto1.get_transition_matrix().size() + auto2.get_transition_matrix().size() - 1, std::vector<std::pair<std::string, bool>>(auto1.get_transition_matrix().size() + auto2.get_transition_matrix().size() - 1, {"0", false}));
    for (int i = 0; i < auto1.get_transition_matrix().size(); i++){
        for (int j = 0; j < auto1.get_transition_matrix().size(); j++){
            transition_matrix[i][j].first = auto1.get_transition_matrix()[i][j].first;
        }
    }
    for (int i = 1; i < auto2.get_transition_matrix().size(); i++){
        for (int j = 1; j < auto2.get_transition_matrix().size(); j++){
            transition_matrix[auto1.get_transition_matrix().size() + i - 1][auto1.get_transition_matrix().size() + j - 1].first = auto2.get_transition_matrix()[i][j].first;
        }
    }
    for (int i = 0; i < auto1.get_transition_matrix().size(); i++){
        for (int j = 1; j < auto2.get_transition_matrix().size(); j++){
            if (auto1.get_end_states()[i] != 0) {
                transition_matrix[i][auto1.get_transition_matrix().size() + j - 1].first = auto2.get_transition_matrix()[0][j].first;
            }
        }
    }

    std::vector<int> end_states (auto1.get_end_states().size() + auto2.get_end_states().size() - 1, 0);
    if (auto2.get_end_states()[0] == 0){
        for (int i = 1; i < auto2.get_end_states().size(); i++){
            end_states[auto1.get_end_states().size() + i - 1] = auto2.get_end_states()[i];
        }
    } else {
        for (int i = 0; i < auto1.get_end_states().size(); i++){
            end_states[i] = auto1.get_end_states()[i];
        }
        for (int i = 1; i < auto2.get_end_states().size(); i++){
            end_states[auto1.get_end_states().size() + i - 1] = auto2.get_end_states()[i];
        }
    }
    return {start_states, transition_matrix, end_states};
}

automaton regex_2_automato(TreeNode* node){
    if (node->data.second == "UNARY") {
        auto a = regex_2_automato(node->left);
        return iteration_automaton(a);
    }
    if (node->data.first == CONCAT_OP){
        auto a = regex_2_automato(node->left);
        auto b = regex_2_automato(node->right);
        return concat_automatons(a, b);
    }
    if (node->data.first == "|"){
        auto a = regex_2_automato(node->left);
        auto b = regex_2_automato(node->right);
        return alternative_automatons(a, b);
    }
    if (node->data.first == INTERSECT_OP){
        auto a = regex_2_automato(node->left);
        auto b = regex_2_automato(node->right);
        return intersect_automatons(a, b);
    }
    return FFL(node->data).ffl_2_glushkov();
}

void replace_dots(std::vector <std::pair <std::string, std::string > >& lexemes) {
    std::set <std::string> terms;
    for (const auto& elem : lexemes){
        if (elem.second == "TERM") {
            terms.insert(elem.first);
        }
    }
    std::vector <std::pair <std::string, std::string > > r = {{"(", "BRACKET"}};
    for (const auto& elem : terms) {
        if (r.size() > 1) r.emplace_back("|", "BINARY");
        r.emplace_back(elem, "TERM");
    }
    r.emplace_back(")", "BRACKET");
    bool f;
    while(true) {
        f = false;
        for (int i = 0; i < lexemes.size(); i++) {
            if (lexemes[i].second == "DOT") {
                lexemes.erase(lexemes.begin() + i);
                lexemes.insert(lexemes.begin() + i, r.begin(), r.end());
                f = true;
                break;
            }
        }
        if (!f) break;
    }
}

void replace_lookahead(std::vector <std::pair <std::string, std::string > >& lexemes, int pos){
    int balance = 1;
    bool end_line_flag = false;
    int pos2 = -1;
    int bracket_pos = pos - 1;
    lexemes.insert(lexemes.begin() + bracket_pos, {"(", "BRACKET"});
    pos++;
    lexemes.erase(lexemes.begin()+pos);
    for (int i = pos; i < lexemes.size(); i++) {
        if (lexemes[i].first == "(") balance++;
        if (lexemes[i].first == ")") balance--;
        if (balance == 0){
            if (lexemes[i - 1].second == "END-LINE"){
                end_line_flag = true;
                lexemes.erase(lexemes.begin()+i-1);
                pos2 = i;
            }
            else pos2 = i + 1;
            break;
        }
    }
    assert(pos2 != -1);
    lexemes.erase(lexemes.begin() + pos2);
    if (!end_line_flag){
        lexemes.insert(lexemes.begin()+pos2, {CONCAT_OP, "CONCAT"});
        pos2++;
        lexemes.insert(lexemes.begin()+pos2, {".", "DOT"});
        pos2++;
        lexemes.insert(lexemes.begin()+pos2, {"*", "UNARY"});
        pos2++;
    }
    lexemes.insert(lexemes.begin()+pos2, {INTERSECT_OP, "INTERSECT"});

    pos2++;

    int f = 0;
    for (int i = pos2; i < lexemes.size(); i++){
        if (lexemes[i].first == "*" || lexemes[i].first == CONCAT_OP || lexemes[i].second == "TERM") continue;
        if (lexemes[i].first == "("){
            int b = 1;
            i++;
            while(b != 0){
                if (lexemes[i].first == "(") b++;
                if (lexemes[i].first == ")") b--;
                i++;
            }
        }
        else{
            lexemes.insert(lexemes.begin() + i, {")", "BRACKET"});
            f = 1;
            break;
        }
    }

    if (f == 0) lexemes.emplace_back(")", "BRACKET");
}

std::vector <std::pair <std::string, std::string> > lexer(const std::string& regex) {
    std::vector <std::pair <std::string, std::string> > res;
    std::string s;
    int balance = 0;

    for (int i = 0; i < regex.size(); i++) {
        s = regex[i];
        if (s == "^") continue;
        else if (s == ")" or s == "(") {
            res.emplace_back(s, "BRACKET");
            if (s == "(") balance++;
            if (s == ")") balance--;
            if (balance < 0) throw std::invalid_argument("Bad bracket balance");
        } else if (s == "$") {
            if (i == regex.size() - 1) continue;
            res.emplace_back(s, "END-LINE");
        } else if (s == "|") {
            res.emplace_back(s, "BINARY");
        } else if (regex[i] == '?' && i < regex.size() - 1 && regex[i + 1] == '=') {
            res.emplace_back("?=", "LOOKAHEAD");
            i++;
        } else if (s == CONCAT_OP) {
            res.emplace_back(CONCAT_OP, "CONCAT");
        } else if (s == "*") {
            res.emplace_back("*", "UNARY");
        } else {
            res.emplace_back(s, "TERM");
        }
    }
    if (balance != 0) throw std::invalid_argument("Bad bracket balance");

    for (int i = 0; i < res.size() - 1; i++){
        if (res[i].second == "TERM" && res[i + 1].second == "TERM"      // a · b
            || res[i].first == ")" && res[i + 1].first == "("           // ) · (
            || res[i].second == "UNARY" && res[i + 1].first == "("      // * · (
            || res[i].second == "TERM" && res[i + 1].first == "("       // a · (
            || res[i + 1].second == "TERM" && res[i].first == ")"       // ) · a
            || res[i].first == "*" && res[i+1].second == "TERM"){       // * · a
            res.insert(res.begin()+i+1, {CONCAT_OP, "CONCAT"});
        }
    }
    //for (const auto& i : res){
    //     std::cout << i.first << " ";
    //}
    //std::cout << std::endl;

    bool f;
    while(true){
        f = false;
        for (int i = 0; i < res.size(); i++){
            if (res[i].second == "LOOKAHEAD"){
                replace_lookahead(res, i);
                f = true;
                break;
            }
        }
        if (!f) break;
    }
    //for (const auto& i : res){
    //    std::cout << i.first << " ";
    // }
    //std::cout << std::endl;
    replace_dots(res);

    return res;
}

int get_priority(const std::string& op){
    if (op == "|") return 4;
    if (op == CONCAT_OP) return 2;
    if (op == "*") return 1;
    if (op == INTERSECT_OP) return 3;
    return 5;
}

std::vector <std::pair <std::string, std::string> > to_postfix(const std::vector <std::pair <std::string, std::string > >& lexemes){
    std::vector <std::pair <std::string, std::string> > res;
    std::stack <std::pair <std::string, std::string> > st;
    for (const auto& lexeme : lexemes) {
        if (lexeme.first == "(") st.push(lexeme);

        else if (lexeme.first == ")") {
            while(st.top().first != "(") {
                res.push_back(st.top());
                st.pop();
            }
            st.pop();
        }

        else if (lexeme.second == "TERM" || lexeme.second == "END-LINE") {
            res.push_back(lexeme);
        }

        else {
            if (lexeme.second != "UNARY")
                while (!st.empty() && get_priority(lexeme.first) >= get_priority(st.top().first)) {
                    res.push_back(st.top());
                    st.pop();
                }
            st.push(lexeme);
        }
    }

    while (!st.empty()) {
        res.push_back(st.top());
        st.pop();
    }

    return res;
}

void automaton::dfs_transpon(int vertex) {
    this->visited[vertex] = true;
    for (int i = 0; i < this->transition_matrix[vertex].size(); i++){
        if (this->transition_matrix[i][vertex].first != "0" && !this->visited[i]){
            dfs_transpon(i);
        }
    }
}

std::vector<std::string> get_alphabet(automaton a){
    std::vector<std::string> res;
    for (int i = 0; i < a.get_transition_matrix().size(); i++){
        for (int j = 0; j < a.get_transition_matrix().size(); j++){
            if (a.get_transition_matrix()[i][j].first == "0"){
                continue;
            }else if (res.empty()){
                res.push_back(a.get_transition_matrix()[i][j].first);
            }else if (!(*std::find(res.begin(), res.end(), a.get_transition_matrix()[i][j].first) == a.get_transition_matrix()[i][j].first)){
                res.push_back(a.get_transition_matrix()[i][j].first);
            }
        }
    }
    return res;
}

automaton automaton::get_addition_automaton(){
    std::vector<std::string> alphabet = get_alphabet({start_states, transition_matrix, end_states});

    std::vector<int> new_start_states = start_states;
    new_start_states.push_back(0);

    std::vector<std::vector<std::pair<std::string, bool>>> new_transition_matrix = transition_matrix;
    for (auto & i : new_transition_matrix){
        i.emplace_back("0", false);
    }
    new_transition_matrix.emplace_back(transition_matrix.size() + 1, std::pair<std::string, bool>("0", false));

    std::vector<int> new_end_states = end_states;
    new_end_states.push_back(0);

    std::vector <bool> new_visited = visited;
    new_visited.push_back(false);

    for (int i = 0; i < transition_matrix.size(); i++){
        std::vector<std::string> go_to_trap;
        for (const auto & j : alphabet){
            bool flag = false;
            for (int k = 0; k < transition_matrix.size(); k++){
                if (transition_matrix[i][k].first == j){
                    flag = true;
                    break;
                }
            }
            if (!flag){
                go_to_trap.push_back(j);
            }
        }
        std::string trap_way;
        if (go_to_trap.empty()){
            continue;
        } else if (go_to_trap.size() == 1){
            trap_way = go_to_trap[0];
        } else {
            trap_way = go_to_trap[0];
            for (int j = 1; j < go_to_trap.size(); j++){
                trap_way += "|" + go_to_trap[j];
            }
        }
        new_transition_matrix[i][new_transition_matrix.size() - 1].first = trap_way;
    }

    for (int i = 0; i < new_end_states.size(); i++){
        if (new_end_states[i]){
            for (int j = 0; j < new_transition_matrix.size(); j++){
                new_transition_matrix[i][j].first = "0";
            }
            dfs_transpon(i);
        }
    }

    for (int i = 0; i < visited.size(); i++){
        if (!(visited[i])){
            new_end_states[i] = 1;
        }
    }
    new_end_states[new_end_states.size() - 1] = 1;
    for(auto && i : this->visited){
        i = false;
    }

    return {new_start_states, new_transition_matrix, new_end_states, new_visited};
}