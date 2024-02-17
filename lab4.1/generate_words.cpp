#include <utility>

struct Rule;

//bool operator< (const std::string& s1, const std::string& s2) {
//    if (s1.size() != s2.size()) {
//        return s1.size() < s2.size();
//    }
//    for (int i = 0; i < s1.size(); i++) {
//        if (s1[i] != s2[i]) {
//            return s1[i] < s2[i];
//        }
//    }
//    return true;
//}
//
//bool operator> (const std::string& s1, const std::string& s2) {
//    if (s1.size() != s2.size()) {
//        return s1.size() < s2.size();
//    }
//    for (int i = 0; i < s1.size(); i++) {
//        if (s1[i] != s2[i]) {
//            return s1[i] > s2[i];
//        }
//    }
//    return true;
//}

auto cmp = [](std::string a, std::string b) {
    if (a.size() != b.size()) {
        return a.size() < b.size();
    }
    for (int i = 0; i < a.size(); i++) {
        if (a[i] != b[i]) {
            return a[i] < b[i];
        }
    }
    return true;
};

class WordsGen{
public:
    std::vector <Rule> G;
    std::set <std::string, decltype(cmp)> words;

    explicit WordsGen(std::vector <Rule> _rules) : G(std::move(_rules)){}

    static bool isWordComplete(const std::string& word) {
        for (auto letter : word) {
            if (isupper(letter)) return false;
        }
        return true;
    }

    static std::string replaceLetterByRule(std::string word, int pos, const Rule& rule) {
        std::string s;
        for (const auto& letter : rule.right) {
            s += letter;
        }
        word.replace(pos, 1, s);
        return word;
    }

    void genWordsRec(const std::string& word, int k) {
        //std::cout << word << std::endl;
        if (isWordComplete(word)){
            words.insert(word);
            return;
        }

        if (word.size() > k) return;

        for (int i = 0; i < word.size(); i++){
            if (isupper(word[i])) {
                for (int j = 0; j < G.size(); j++) {
                    if (G[j].left[0] == word[i]) {
                        genWordsRec(replaceLetterByRule(word, i, G[j]), k);
                    }
                }
                break;
            }
        }
    }

    static std::string applyFold(std::string word) {
        std::vector <std::pair <char, int> > parsed;
        for (int i = 0; i < word.size(); i++){
            char letter = word[i];
            int count = 0;
            int j = i;
            for (; j < word.size(); j++){
                if (word[j] == letter) count++;
                else break;
            }
            parsed.emplace_back(letter, count);
            i = j-1;
        }

        std::string res;
        for (auto elem : parsed) {
            if (elem.second == 1)  {
                res += elem.first;
            }
            else {
                res += "(" + std::string(1, elem.first) + "^" + std::to_string(elem.second) + ")";
            }
        }
        return res;
    }

    std::vector<std::string> getWords(int k) {
        std::vector <std::string> res;
        std::vector <Rule> start_rules;
        for (const auto & i : G){
            if (i.left[0] == 'S'){
                start_rules.push_back(i);
                break;
            }
        }
        for (const auto& start_rule : start_rules) {
            std::string w;
            for (const auto &s: start_rule.right) {
                w += s;
            }
            res.push_back(w);
        }
        for (const auto& w : res) {
            genWordsRec(w, k);
        }
        std::vector<std::string> res_words;
        for (auto& word : words) {
            res_words.push_back(applyFold(word));
        }
        return res_words;
    }
};

