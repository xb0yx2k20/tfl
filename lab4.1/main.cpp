#include "main_algo.cpp"
#include "generate_words.cpp"

int main() {
    std::ifstream fin("input.txt");
    assert(fin.is_open());
    std::string input;
    std::string R;
    std::vector <Rule> G;
    fin >> R;
    std::string left;
    std::vector <std::string> right;
    std::string s;
    getline(fin, input);
    while(getline(fin, input)) {
        if (input.empty()) continue;
        std::stringstream ss(input);
        ss >> left;
        ss >> s; // skip "->"
        while(ss >> s) {
            right.emplace_back(s);
        }
        G.push_back({left, right});
        right.clear();
    }

    deleteNonGenerativeRules(G);
    deleteNonAchievableRules(G);

    for (const auto& rule : G) {
        showRule(rule);
    }

//    WordsGen generator(G);
//    std::vector <std::string> words = generator.getWords(6);
//    for (auto word: words) {
//        std::cout << word << std::endl;
//    }



    // regex to automaton
    std::vector <std::pair <std::string, std::string > > lexemes = lexer(R);
    std::vector <std::pair <std::string, std::string > > postfix = to_postfix(lexemes);
    TreeNode* tree = build_tree(postfix);
    auto res = regex_2_automato(tree);
//    res.show_automaton();
//    res.show_like_arrows();
    auto res_addit = res.get_addition_automaton();
//    res_addit.show_automaton();
//    res_addit.show_like_arrows();
//    automaton res = automaton({1, 0}, {{{"a", false}, {"b", false}}, {{"0", false}, {"b", false}}}, {0, 1});
    auto addit_intersect_g = main_algo(res_addit, G);
    WordsGen generator(addit_intersect_g);
    int k = 6;
    std::vector <std::string> words = generator.getWords(k);
    if (words.empty() || (words.size() == 1 and words[0].empty())){
        std::cout << "\n";
        auto default_intersect_g = main_algo(res, G);
        for (auto r : default_intersect_g){
            showRule(r);
        }
//        WordsGen generator_2(default_intersect_g);
//        std::vector <std::string> words_2 = generator_2.getWords(k);
//        for (const auto& word : words_2){
//            std::cout << word << std::endl;
//        }
    } else {
        std::cout << "ERROR" << std::endl;
    }
    return 0;
}