/* Clifford Ressel (cressel@andrew.cmu.edu) */

/* A context sensitive grammar (CSG) parser
 * for 15-453 final project (fall, 2016).
 *
 * We're going to ONLY work with grammars in Kuroda normal form (KNF).
 * (a reasonable format, as every CSG can be expressed in KNF,
 * and it's very useful for our algorithm)
 *
 * For more details on the input, read through tests/example_abc.csg
 *
 * If you find any buggy behavior it's quite likely a fault of the input
 * parsing and not the algorithm itself.
 *
 * Also please pardon the comments with {{{ / }}}; I use these vim
 * folds to easily navigate large files (feel free to use them as well)
 */

#include <stdlib.h>
#include <stdio.h>
#include <readline/readline.h>
#include <readline/history.h>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <utility>
#include <iostream>
#include <fstream>
#include <cstddef>
#include <sstream>

// types and setup {{{

typedef std::string	symbol;
typedef std::vector<symbol> word;
const symbol S = "S";
const symbol NONE = "NONE";

/* We are in KNF, so each side of a rule will never have more than
 * two symbols. So any rule could be a pair of pairs of symbols:
 * side<A,B> 	--> side<C,D>
 * side<A,NONE>	--> side<A,B>
 * side<A,NONE>	--> side<a,NONE> */
typedef std::pair<symbol,symbol> side;
typedef std::pair<side,side> rule;

/* And for returning our results:
 * (this is applying the rule to some input and getting the word) */
typedef std::pair<rule,word> change;


/* Hashing for the vectors of words that will end up in my memo */
template <class T>
inline void hash_combine(std::size_t& seed, T const& v)
{
    seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}
namespace std
{
    template<typename T>
    struct hash<vector<T>>
    {
        typedef vector<T> argument_type;
        typedef std::size_t result_type;
        result_type operator()(argument_type const& in) const
        {
            size_t size = in.size();
            size_t seed = 0;
            for (size_t i = 0; i < size; i++)
                // Combine the hash of the current vector with the
				// hashes of the previous ones
                hash_combine(seed, in[i]);
            return seed;
        }
    };
}

// }}}

// Grammar class {{{
/* The context sensitive grammar itself
 * constructor: Grammar(variables, terminals, rules)
 * parsing: parse(word)
 */
class Grammar {
	public:
		// store our variables and terminals
		std::vector<symbol> variables;
		std::vector<symbol> terminals;
		// quicker lookup for checking nature of a symbol
		std::map<symbol,bool> isTerminal;
		std::map<symbol,bool> isVariable;
		// given a terminal, return possible variables it came from
		std::map<symbol, std::vector<symbol> > termToVars;
		// all the rules in the grammar except terminal conversions
		std::vector<rule> rules;
		std::vector<rule> Srules;
		// and a global hash table for parsing to avoid infinite loops
		std::unordered_map<word,bool> memo;


		// our constructor
		Grammar(std::vector<symbol> vs,
				std::vector<symbol> ts,
				std::vector<rule> rs) {

			std::cout << "... storing variables ..." << std::endl;

			// save our set of variables
			variables = vs;
			std::vector<symbol>::iterator it1;
			for (it1 = vs.begin(); it1 != vs.end(); ++it1) {
				// save this in our lookup
				symbol v = *it1;
				isVariable[v] = true;
			}

			std::cout << "... storing terminals ..." << std::endl;

			// save our set of terminals
			terminals = ts;
			std::vector<symbol>::iterator it2;
			for (it2 = ts.begin(); it2 != ts.end(); ++it2) {
				// save this in our lookup
				symbol t = *it2;
				isTerminal[t] = true;

				// look through the rules for any variables
				// going to this terminal symbol
				std::vector<symbol> vars;
				std::vector<rule>::iterator it3;
				for (it3 = rs.begin(); it3 != rs.end(); ++it3) {
					rule r = *it3;
					symbol left1 = r.first.first;
					symbol right1 = r.second.first;
					// something goes to this terminal, so add it
					if (t == right1) {
						vars.push_back(left1);
					}
				}
				// save the variables possible to arrive at this
				// terminal for later parsing
				termToVars[t] = vars;
			}

			std::cout << "... storing rules ..." << std::endl;

			// store every rule that's not working with terminals and
			// keep a special copy of the S rules for a base case in
			// our parsing recursion
			for (unsigned int i = 0; i < rs.size(); i++) {
				std::cout << ".";
				rule r = rs[i];
				symbol left1 = r.first.first;
				symbol left2 = r.first.second;
				symbol right1 = r.second.first;
				symbol right2 = r.second.second;

				if (left1 == "S" && left2 == "NONE"
					&& right1 != "S" && right2 != "S") {
					Srules.push_back(r);
					rules.push_back(r);
				} else {
					std::map<symbol,bool>::iterator it4 =
						isTerminal.find(right1);
					if (it4 != isTerminal.end() && (*it4).second)
						continue;
					else {
						rules.push_back(r);
					}
				}
			}
			std::cout << "done!" << std::endl;
		}

		void printVariables();
		void printTerminals();
		void printTermToVars();
		void printRules();

		std::pair<bool, std::vector<change> > parse_helper(word w);
		void parse(word w);

		// Choices are vectors representing which variables we are
		// replacing the terminals by (in the range of 0 to their
		// termToVars vector length)

		// Returns the word with each terminal replaced by the variable
		// indicated in the choices vector
		word wordFrom(std::vector<int> choices, word w);
		// Returns true and the next selection of variable replacements,
		// or false and all zeros if there is none
		std::pair<bool, std::vector<int> > nextChoice(
				std::vector<int> prev,
				std::vector<int> maxes);
		// Lists the variable to terminal substitutions that have been
		// made to complete a derivation
		void listTerminals(std::vector<int> choice,
				std::vector<int> maxes, word w);
};
// }}}

// parsing functions {{{

// requires w is all terminals
// requires choice and w are same length
word Grammar::wordFrom(std::vector<int> choice, word w) {
	word result;
	for (unsigned int i = 0; i < w.size(); i++) {
		symbol s = w[i];
		std::map<symbol, std::vector<symbol> >::iterator it;
		it = termToVars.find(s);

		if (it == termToVars.end())
			throw std::invalid_argument("word can only contain terminals");

		int c = choice[i];
		// convert to whichever variable in the termToVars vector is
		// indicated by our choice vector
		result.push_back(it->second[c]);
	}
	return result;
}

// requires every value in maxes is strictly greater than in prev
// requires prev and maxes are same length
std::pair<bool, std::vector<int> > Grammar::nextChoice(
		std::vector<int> prev,
		std::vector<int> maxes) {
	// think of this like incrementing a variable-base number
	for (unsigned int i = 0; i < prev.size(); i++) {
		if (prev[i] < maxes[i] - 1) {
			prev[i]++;
			return std::make_pair(true,prev);
		} else {
			prev[i]  = 0;
		}
	}
	return std::make_pair(false,prev);
}

// And here hides the true work of the parsing, the source of all the
// runtime of this damn algorithm, and the entirety of my missed nights
// of sleep on both Thursday and Friday.
// Memoization on this method would be the most significant immediate
// improvement for the runtime. Given the usage of a hash table for
// avoiding infinite loops, this wouldn't be too much of an addition.
std::pair<bool, std::vector<change> > Grammar::parse_helper(word w) {
	//for (unsigned int i = 0; i < w.size(); i++) {
		//std::cout << w[i];
	//}
	//std::cout << std::endl;

	std::vector<change> result;
	// base case: w is equal to the RHS of some rule in Srules
	if (w.size() == 0) return std::make_pair(false, result);
	else if (w.size() <= 2) {
		std::vector<rule>::iterator it;
		for (it = Srules.begin(); it != Srules.end(); ++it) {
			rule r = *it;
			if (w.size() == 1) {
				if (w[0] == r.second.first && r.second.second == "NONE") {
					result.push_back(std::make_pair(r,w));
					return std::make_pair(true, result);
				}
			} else { // size == 2
				if (w[0] == r.second.first && w[1] == r.second.second) {
					result.push_back(std::make_pair(r,w));
					return std::make_pair(true, result);
				}
			}
		}
	}

	// to recurse, we:
	// for each rule r:
	//   for each way r can be applied
	//   recurse on each application
	//     passing back up if we found a good derivation below
	//     backtracking to next application of r if all false below
	// and checking in with our memo the whole time to ensure no
	// infinite loops

	std::vector<rule>::iterator it;
	for (it = rules.begin(); it != rules.end(); ++it) {
		rule r = *it;
		symbol left1 = r.first.first;
		symbol left2 = r.first.second;
		symbol right1 = r.second.first;
		symbol right2 = r.second.second;

		if (right2 == "NONE") {
			for (unsigned int i = 0; i < w.size(); i++) {
				if (w[i] == right1) {

					w[i] = left1;

					// checking whether we've made this call before
					// (i.e. checking to avoid an infinite loop)
					auto check = memo.find(w);
					if (check != memo.end()) {
						if (check->second) {
							w[i] = right1;
							continue;
						}
					}

					memo.insert({w, true});
					std::pair<bool,std::vector<change>> recurse =
						parse_helper(w);

					if (recurse.first) {
						w[i] = right1;
						change thisC = std::make_pair(r,w);
						recurse.second.push_back(thisC);
						return std::make_pair(true,recurse.second);
					} else {
						w[i] = right1;
					}
				}
			}
		} else {
			for (unsigned int i = 0; i < w.size() - 1; i++) {
				if (w[i] == right1 && w[i+1] == right2) {
					w[i] = left1;
					if (left2 == "NONE")
						w.erase(w.begin() + i + 1);
					else
						w[i+1] = left2;

					auto check = memo.find(w);
					if (check != memo.end()) {
						if (check->second) {
							w[i] = right1;
							w[i+1] = right2;
							continue;
						}
					}

					memo.insert({w, true});
					std::pair<bool, std::vector<change> > recurse =
						parse_helper(w);

					if (recurse.first) {
						w[i] = right1;
						if (left2 == "NONE")
							w.insert(w.begin() + i + 1, right2);
						else
							w[i+1] = right2;
						change thisC = std::make_pair(r,w);
						recurse.second.push_back(thisC);
						return std::make_pair(true,recurse.second);
					} else {
						w[i] = right1;
						w[i+1] = right2;
					}
				}
			}
		}
	}

	return std::make_pair(false,result);
}

void printDerivation(std::vector<change> derivation) {
	std::vector<change>::iterator it;
	for (it = derivation.begin(); it != derivation.end(); ++it) {
		change c = *it;
		rule r = c.first;
		symbol l1 = r.first.first;
		symbol l2 = r.first.second;
		symbol r1 = r.second.first;
		symbol r2 = r.second.second;
		std::cout << l1 << " ";
		if (l2 != "NONE") std::cout << l2;
		std::cout << " --> " << r1 << " ";
		if (r2 != "NONE") std::cout << r2;
		std::cout << " to create: " ;

		word w = c.second;
		word::iterator it1;
		for (it1 = w.begin(); it1 != w.end(); ++it1) {
			symbol s = *it1;
			std::cout << s << " ";
		}

		std::cout << std::endl;
	}
}

void Grammar::listTerminals(std::vector<int> choice,
		std::vector<int> maxes, word w) {
	std::cout << "Replace terminals:" << std::endl;

	for (unsigned int i = 0; i < choice.size(); i++) {
		if (choice[i] > 0) {
			choice[i]--;
			break;
		} else {
			choice[i] = maxes[i] - 1;
		}
	}

	for (unsigned int i = 0; i < w.size(); i++) {
		symbol s = w[i];
		std::map<symbol, std::vector<symbol> >::iterator it;
		it = termToVars.find(s);

		if (it == termToVars.end())
			throw std::invalid_argument("word can only contain terminals");

		int c = choice[i];
		std::cout << it->second[c] << " --> " << s << std::endl;
	}
}

void Grammar::parse(word w) {

	// first we need to generate all our starting strings
	// this is something like
	// termToVars[a] X termToVars[b] X ...
	std::pair<bool, std::vector<int> > choice;
	choice.second.assign(w.size(), 0);

	std::vector<int> maxes;
	for (unsigned int i = 0; i < w.size(); i++) {
		symbol s = w[i];
		std::map<symbol, std::vector<symbol> >::iterator it;
		it = termToVars.find(s);

		if (it == termToVars.end())
			throw std::invalid_argument("word can only contain terminals");
		maxes.push_back(it->second.size());
	}

	word w1 = wordFrom(choice.second, w);
	memo = {{w1,true}};

	std::pair<bool, std::vector<change> > derivation =
		parse_helper (w1);

	// while we have no derivation and more starts to check
	while (!derivation.first && choice.first) {
		word wNew = wordFrom(choice.second, w);
		memo.insert({wNew,true});

		derivation = parse_helper (wNew);
		choice = nextChoice(choice.second,maxes);
	}

	if (derivation.first) {
		std::cout << "Word derived successfully!" << std::endl;
		printDerivation(derivation.second);
		listTerminals(choice.second,maxes,w);
	} else {
		std::cout << "No derivation possible." << std::endl;
	}
}
// }}}

// print helpers {{{

void Grammar::printVariables() {
	std::cout << "Variables:" << std::endl << "--------" << std::endl;
	std::vector<symbol>::iterator it;
	for (it = variables.begin(); it != variables.end(); ++it) {
		symbol s = *it;
		std::cout << s << std::endl;
	}
	std::cout << "--------" << std::endl;
}

void Grammar::printTerminals() {
	std::cout << "Terminal:" << std::endl << "--------" << std::endl;
	std::vector<symbol>::iterator it;
	for (it = terminals.begin(); it != terminals.end(); ++it) {
		symbol s = *it;
		std::cout << s << std::endl;
	}
	std::cout << "--------" << std::endl;
}

void Grammar::printTermToVars() {
	std::cout << "Terminal to Vars:" << std::endl
		<< "--------" << std::endl;
	std::map<symbol, std::vector<symbol> >::iterator it;
	for (it = termToVars.begin(); it != termToVars.end(); ++it) {
		std::pair<symbol, std::vector<symbol> > p = *it;
		std::cout << p.first << ": ";
		std::vector<symbol>::iterator it1;
		for (it1 = p.second.begin(); it1 != p.second.end(); ++it1) {
			symbol s = *it1;
			std::cout << s << " ";
		}
		std::cout << std::endl;
	}
	std::cout << "--------" << std::endl;
}

void Grammar::printRules() {
	std::cout << "Rules:" << std::endl << "--------" << std::endl;
	std::vector<rule>::iterator it;
	for (it = rules.begin(); it != rules.end(); ++it) {
		rule r = *it;
		symbol l1 = r.first.first;
		symbol l2 = r.first.second;
		symbol r1 = r.second.first;
		symbol r2 = r.second.second;
		std::cout << l1 << " " << l2 << " --> "
			<< r1 << " " << r2 << std::endl;
	}
	std::cout << "--------" << std::endl;
}

// }}}

// CLI {{{

rule ruleOf(std::string l1, std::string l2,
			std::string r1, std::string r2) {
	return std::make_pair(
			std::make_pair (l1,l2),
			std::make_pair (r1,r2)
		);
}

int main () {
	Grammar *g = NULL;
	while (true) {

		char* line = readline("> ");
		if (!line) {
			if (g) delete g;
			return 1;
		}
		if (*line) add_history(line);

		std::string input = std::string(line);
		if (input == "exit"
	     || input == "quit"
		 || input == "q") {
			free(line);
			if (g) delete g;
			return 0;
		} else if (input == "help") {
			std::cout << "Please enter a command to use this CSG parser:"
				<< std::endl << " *  create <grammar file locn>"
				<< std::endl << " *  parse <word>" << std::endl
				<< "(recall that words consist of space separated symbols)"
				<< std::endl
				<< " *  printVariables" << std::endl
				<< " *  printTerminals" << std::endl
				<< " *  printTermToVars" << std::endl
				<< " *  printRules" << std::endl
				<< " *  exit | quit | q" << std::endl;
		} else if (input == "create") {
			char* infilename = readline("create> ");
			if (!infilename) {
				if (g) delete g;
				return 1;
			}
			if (*infilename) add_history(infilename);
			std::cout << "Creating parser..." << std::endl;

			//std::vector<symbol> vs = { "A", "A'", "B", "B'", "C" };
			//std::vector<symbol> ts = { "a", "b", "c" };
			//std::vector<rule> rs;
			//rs.push_back(ruleOf("S","NONE","A'","NONE"));
			//rs.push_back(ruleOf("A'","NONE","A","B'"));
			//rs.push_back(ruleOf("A","NONE","a","NONE"));
			//rs.push_back(ruleOf("B'","NONE","B","C"));
			//rs.push_back(ruleOf("C","NONE","c","NONE"));

			std::vector<symbol> vs;
			std::vector<symbol> ts;
			std::vector<rule> rs;

			std::ifstream infile(infilename);
			std::string fileline;
			bool atRules = false;
			while (std::getline(infile, fileline)) {

				std::string start = fileline.substr(0,1);
				if (atRules == true) {
					std::vector<symbol> rstemp;

					std::istringstream iss(fileline);
					for(std::string next; iss >> next; ) {
						if (next != "-->")
    						rstemp.push_back(next);
					}
					if (rstemp.size() == 2) {
						rs.push_back(ruleOf(rstemp[0], "NONE",
									rstemp[1], "NONE"));
					} else if (rstemp.size() == 3) {
						rs.push_back(ruleOf(rstemp[0], "NONE",
									rstemp[1], rstemp[2]));
					} else if (rstemp.size() == 4) {
						rs.push_back(ruleOf(rstemp[0], rstemp[1],
									rstemp[2], rstemp[3]));
					}

				} else {
					if (start == "#") {
						continue;
					} else if (start == "V") {
						std::string vars = fileline.substr(4);
						std::istringstream iss(vars);
						for(std::string next; iss >> next; )
    						vs.push_back(next);
					} else if (start == "T") {
						std::string ters = fileline.substr(4);
						std::istringstream iss(ters);
						for(std::string next; iss >> next; )
    						ts.push_back(next);
					} else if (start == "R") {
						atRules = true;
						continue;
					}
				}
			}

			g = new Grammar(vs, ts, rs);
		} else if (input == "printVariables") {
			if (g) g->printVariables();
			else std::cout << "Grammar undefined." << std::endl;
		} else if (input == "printTerminals") {
			if (g) g->printTerminals();
			else std::cout << "Grammar undefined." << std::endl;
		} else if (input == "printTermToVars") {
			if (g) g->printTermToVars();
			else std::cout << "Grammar undefined." << std::endl;
		} else if (input == "printRules") {
			if (g) g->printRules();
			else std::cout << "Grammar undefined." << std::endl;
		} else if (input == "parse") {
			if (g) {
				char* line1 = readline("parse> ");
				if (!line1) {
					if (g) delete g;
					return 1;
				}
				if (*line1) add_history(line1);

				std::string input1 = std::string(line1);
				std::vector<std::string> result;
				std::istringstream iss(input1);
				for(std::string input2; iss >> input2; )
    				result.push_back(input2);

				g->parse(result);
			}
			else std::cout << "Grammar undefined." << std::endl;
		} else {
			std::cout << "Input not recognized. "
				<< "See help for valid commands" << std::endl;
		}

		free (line);
	}
}

// }}}

