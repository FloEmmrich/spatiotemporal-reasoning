#include <iostream>
#include <fstream>
#include <queue>
#include <set>
#include <string>
#include <tuple>

// CLASS PROTOTYPES //

class Axiom;
class Theory;


// GLOBAL VARIABLES I //

const int max_size = 10; // maximum column size for grid array


// FUNCTION PROTOTYPES //

std::string getAxiomType(Axiom);
void printGrid(Theory[][max_size], int, int, Axiom, Axiom);


// CLASSES //

class Axiom {
	public:
		Axiom() {
			value = "";
			type = "UNDEF";
			impulse = 0;
		}
		Axiom(std::string v) {
			value = v;
			type = "UNDEF";
			type = getAxiomType(*this);
			if (type == "UNDEF") {
				std::cerr << "[ERROR] Illegal axiom value: " << v << ".\n";
				throw 100;
			}
			impulse = 1;
		}
		void decImpulse(int dir) {
			if (impulse[dir] > 0) {
				impulse[dir]--;
			}
		}
		int[4] getImpulse() const {
			return impulse;
		}
		std::string getType() const {
			return type;
		}
		std::string getValue() const {
			return value;
		}
		Axiom negate() {
			if (type == "PROP") {
				return Axiom("NOT(" + value + ")");
			} else if (type == "NEG") {
				std::string v = value;
				v.erase(v.begin(), v.begin()+4);
				v.erase(v.end()-1, v.end());
				return Axiom(v);
			} else {
				return *this;
			}
		}
		void operator=(const Axiom& r) {
			value = r.value;
			type = getAxiomType(value);
			impulse = r.impulse;
		}
		friend bool operator==(const Axiom& l, const Axiom& r) {
			return l.value == r.value;
		}
		friend bool operator<(const Axiom& l, const Axiom& r) {
			return std::tie(l.type, l.value) < std::tie(r.type, r.value);
		}
	private:
		const std::string types[4] = {"BOUND","NEG","PROP","UNDEF"};
		std::string value;
		std::string type;
		int impulse[4];
};

class Theory {
	public:
		Theory() {
			axioms = std::set<Axiom>();
		}
		Theory(std::set<Axiom> a) {
			axioms = a;
		}
		void addAxiom(Axiom a) {
			axioms.insert(a);
		}
		bool is_inconsistent() {
			std::set<Axiom> rest = axioms;
			for (Axiom ax1 : axioms) {
				rest.erase(ax1);
				for (Axiom ax2 : rest) {
					if (ax1.negate() == ax2) {
						return 1;
					}
				}
			}
			return 0;
		}
		std::set<Axiom*> getAxioms() {
			std::set<Axiom*> ax;
			for (Axiom a : axioms) {
				ax.insert(&a);
			}
			return ax;
		}
		std::set<Axiom> getAxiomSet() {
			return axioms;
		}
	private:
		std::set<Axiom> axioms;
};


// GLOBAL VARIABLES II //

const Axiom boundary("BOUNDARY");


// MAIN //

int main() {
	const int steps = 15;
	
	int n, m;
	std::string line;
	std::ifstream File("../grid.txt");
	File >> n >> m;
	std::cout << "Grid size: " << n << " x " << m << "." << std::endl;
	
	if (m > max_size) {
		std::cerr << "[ERROR] Column size exceeds maximum of " << max_size << ".\n";
		throw 200;
	}
	
	Theory grid[n][max_size];
	for (int j = 0; j < m; j++) {
		grid[0][j].addAxiom(boundary);
		grid[n-1][j].addAxiom(boundary);
	}
	for (int i = 1; i < n-1; i++) {
		grid[i][0].addAxiom(boundary);
		grid[i][m-1].addAxiom(boundary);
	}
	
	int x, y;
	std::string prop;
	while (File >> x >> y >> prop) {
		grid[x][y].addAxiom(Axiom(prop));
	}
	
	File.close();
	
	//Axiom phi("phi");
	//grid[n/2][m/2].addAxiom(phi);
	
	std::cout << "\nInit:\n";
	printGrid(grid, n, m, Axiom("psi"), Axiom("NOT(psi)"));
	
	Theory newGrid[n][max_size];
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < m; j++) {
			newGrid[i][j] = grid[i][j];
		}
	}
	
	std::set<Axiom> axioms;
	std::queue<int> inconsistent;
	Axiom pulseAxiom;
	for (int k = 1; k <= steps; k++) {
		std::cout << "Step " << k << ":\n";
		for (int i = 1; i < n-1; i++) {
			for (int j = 1; j < m-1; j++) {
				if (grid[i][j].is_inconsistent()) {
					inconsistent.push(i);
					inconsistent.push(j);
					continue;
				}
				axioms = grid[i][j].getAxiomSet();
				for (Axiom a : axioms) {
					if (a.getType() != "BOUND") { // TODO: manage impulse
						newGrid[i+1][j].addAxiom(a);
						newGrid[i-1][j].addAxiom(a);
						newGrid[i][j+1].addAxiom(a);
						newGrid[i][j-1].addAxiom(a);
						a.decImpulse();
					}
				}
				grid[i][j] = Theory(axioms);
			}
		}
		
		int x;
		while (!inconsistent.empty()) {
			x = inconsistent.front();
			inconsistent.pop();
			newGrid[x][inconsistent.front()] = Theory();
			inconsistent.pop();
		}
		
		printGrid(newGrid, n, m, Axiom("psi"), Axiom("NOT(psi)"));
		
		axioms = newGrid[5][4].getAxiomSet();
		std::cout << "[INFO] (5,4) ";
		for (Axiom a : axioms) {
			std::cout << a.getValue() << ":" << a.getImpulse() << "; ";
		}
		std::cout << std::endl;
		axioms = newGrid[4][4].getAxiomSet();
		std::cout << "[INFO] (4,4) ";
		for (Axiom a : axioms) {
			std::cout << a.getValue() << ":" << a.getImpulse() << "; ";
		}
		std::cout << std::endl;
		axioms = newGrid[2][2].getAxiomSet();
		std::cout << "[INFO] (2,2) ";
		for (Axiom a : axioms) {
			std::cout << a.getValue() << ":" << a.getImpulse() << "; ";
		}
		std::cout << std::endl;
		
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < m; j++) {
				grid[i][j] = newGrid[i][j];
			}
		}
	}
	
	return 0;
}


// FUNCTIONS //

std::string getAxiomType(Axiom axiom) {
	std::string type = axiom.getType();
	if (type != "UNDEF") {
		return type;
	}
	std::string value = axiom.getValue();
	if (value.empty()) {
		return "UNDEF";
	} else if (value == "BOUNDARY") {
		return "BOUND";
	} else if (value.substr(0,4) == "NOT(" && value.back() == ')') {
		return "NEG";
	} else if (value.find("()") == std::string::npos) {
		return "PROP";
	} else {
		return "UNDEF";
	}
}

void printGrid(Theory grid[][max_size], int n, int m, Axiom ax1, Axiom ax2) {
	std::set<Axiom> axioms;
	std::cout << std::endl;
	for (int j = 0; j < m; j++) {
		for (int i = 0; i < n; i++) {
			axioms = grid[i][j].getAxiomSet();
			if (axioms.find(boundary) != axioms.end()) {
				std::cout << "X ";
			} else if (axioms.find(ax1) != axioms.end()) {
				std::cout << "1 ";
			} else if (axioms.find(ax2) != axioms.end()) {
				std::cout << "2 ";
			} else {
				std::cout << "0 ";
			}
		}
		std::cout << std::endl;
	}
	std::cout << std:: endl;
}