#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include <map>

// za dva atoma treba proveriti da li
// uopstena supstitucija je njihov unifikator
// samo uradimo supstituciju na oba
// ako dobijemo isto, super
// ako ne, nije super

class Term;
using T = std::shared_ptr<Term>;

class Term : public std::enable_shared_from_this<Term> {
	public:
		virtual void print(std::ostream&) = 0;
		friend std::ostream& operator<<(std::ostream& os, T& t) {
			t->print(os);
			return os;
		}
		
		virtual bool operator==(const T&) const = 0;
		
		friend bool operator==(const T& t1, const T& t2) {
			return *t1 == t2;
		}
		
		class Comp {
			public:
				bool operator()(const T& t1, const T& t2) const {
					return t1 == t2;
			}
		};
		
		virtual T substitute(const T&, const T&) = 0;


};

class ConstantTerm : public Term {
	public:
		ConstantTerm(std::string& n): name(n) {}
		
		void print(std::ostream& os) {
			os << name;
		}
		
		std::string get_name() {
			return name;
		}
		
		bool operator==(const T& t) const {
			auto x = std::dynamic_pointer_cast<ConstantTerm>(t);
			return x != nullptr && x->get_name() == name;
		
		}
		
		T substitute(const T&, const T&) {
			return shared_from_this();
		}
	
	
	private:
		std::string name;
};


class VariableTerm : public Term {
	public:
		VariableTerm(std::string& n): name(n) {}
		
		void print(std::ostream& os) {
			os << name;
		}
		
		std::string get_name() {
			return name;
		}
		
		bool operator==(const T& t) const {
			auto x = std::dynamic_pointer_cast<VariableTerm>(t);
			return x != nullptr && x->get_name() == name;
		
		}
		
		T substitute(const T& t1, const T& t2) {
			auto x = std::dynamic_pointer_cast<VariableTerm>(t1);
			if(x == nullptr || x->get_name() != name) return shared_from_this();
			return t2;
		}
	
	
	private:
		std::string name;
};

class FunctionTerm : public Term {
	public:
		FunctionTerm(std::string& s, std::vector<T>& a):
			symbol(s), args(a) {}
			
		void print(std::ostream& os) {
			os << symbol << '(';
			for(unsigned i = 0; i < args.size(); i++) {
				os << args[i] << ((i == args.size() - 1)? ")" : ", ");
			}
		}
		
		std::string get_symbol() {
			return symbol;
		}
		
		std::vector<T> get_args() {
			return args;
		}
		
		friend bool operator==(const std::vector<T>& t1, const std::vector<T>& t2) {
			if(t1.size() != t2.size()) return false;
			
			auto it1 = t1.begin(), it2 = t2.begin();
			
			for(; it1 != t1.end() && it2 != t2.end(); ++it1, ++it2) {
				if(*it1 != *it2) return false;
			}
			
			return true;
		}
		
		bool operator==(const T& t) const {
			auto x = std::dynamic_pointer_cast<FunctionTerm>(t);
			return x != nullptr && x->get_symbol() == symbol && x->get_args() == args;
		
		}
		
		T substitute(const T& t1, const T& t2) {
			std::vector<T> new_args = {};
			
			for(const auto& a : args) {
				new_args.push_back(a->substitute(t1, t2));
			}
			
			return std::make_shared<FunctionTerm>(symbol, new_args);
		}
	
	
	private:
		std::string symbol;
		std::vector<T> args;
};

class Atom;
using A = std::shared_ptr<Atom>;

class Atom {
	public:
		Atom(std::string& s, std::vector<T>& a):
			symbol(s), args(a) {}
			
		void print(std::ostream& os) {
			os << symbol << '(';
			for(unsigned i = 0; i < args.size(); i++) {
				os << args[i] << ((i == args.size() - 1)? ")" : ", ");
			}
		}
		
		friend std::ostream& operator<<(std::ostream& os, A& a) {
			a->print(os);
			return os;
		}
		
		std::string get_symbol() {
			return symbol;
		}
		
		std::vector<T> get_args() {
			return args;
		}
		
		bool operator==(const A& a) const {
			return a->get_symbol() == symbol && a->get_args() == args;
		}
		
		friend bool operator==(const A& a1, const A& a2) {
			return *a1 == a2;
		}
		
		A substitute(const T& t1, const T& t2) {
			std::vector<T> new_args;
			// samo prosledimo svakom termu
			for(const auto& t : args) {
				new_args.push_back(t->substitute(t1, t2));
			}
			return std::make_shared<Atom>(symbol, new_args);
		}
		
		friend bool is_unifiable(A& a1, A& a2, std::map<T, T>& unifier) {
			// samo unifikatorom posmenjujemo u oba
			for(auto it = unifier.begin(); it != unifier.end(); ++it) {
				a1->substitute(it->first, it->second);
				a2->substitute(it->first, it->second);
			} 
			return a1 == a2;
		}
	
	
	private:
		std::string symbol;
		std::vector<T> args;
};


int main() {

	std::string x1 = "x";
	std::string c1 = "c";
	std::string y1 = "y";
	std::string f = "f";

	T x = std::make_shared<VariableTerm>(x1);
	T c = std::make_shared<VariableTerm>(c1);
	T y = std::make_shared<VariableTerm>(y1);
	std::vector<T> v1 = {x, y};
	std::vector<T> v2 = {x, y};
	T f1 = std::make_shared<FunctionTerm>(f, v1);
	T f2 = std::make_shared<FunctionTerm>(f, v2);
	

	std::cout << x << '\n' << c << '\n' << y << '\n' << f1 << '\n';
	std::cout << (f1 == f2) << '\n' << (f1 == c) << '\n';
	std::map<T, T> unifier;
	
	std::vector<T> a_args = {x, y, f1};
	std::string p1 = "p";
	A a = std::make_shared<Atom>(p1, a_args);
	std::cout << a << '\n';
	A a1 = a->substitute(x, c);
	std::cout << a1 << '\n';

	return 0;
}
