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
std::set<Axiom> getRuleBody(Axiom);
Axiom getRuleHead(Axiom);
void printGrid(Theory[][max_size], int, int, std::string, std::string);


// CLASSES //

class Axiom {
	public:
		Axiom() {
			value = "";
			type = "UNDEF";
			impulse[0] = impulse[1] = impulse[2] = impulse[3] = 0;
			source[0] = source[1] = -1;
		}
		Axiom(std::string v, int x, int y) {
			value = v;
			type = "UNDEF";
			type = getAxiomType(*this);
			if (type == "UNDEF") {
				std::cerr << "[ERROR] Illegal axiom value: " << v << ".\n";
				throw 100;
			}
			impulse[0] = impulse[1] = impulse[2] = impulse[3] = 1;
			source[0] = x;
			source[1] = y;
		}
		Axiom(std::string v) {
			value = v;
			type = "UNDEF";
			type = getAxiomType(*this);
			if (type == "UNDEF") {
				std::cerr << "[ERROR] Illegal axiom value: " << v << ".\n";
				throw 100;
			}
			impulse[0] = impulse[1] = impulse[2] = impulse[3] = 1;
			source[0] = -1;
			source[1] = -1;
		}
		void decImpulse(int dir) {
			if (impulse[dir] > 0) {
				impulse[dir]--;
			}
		}
		void decImpulse() {
			for (int i = 0; i < 4; i++) {
				if (impulse[i] > 0) {
					impulse[i]--;
				}
			}
		}
		std::set<Axiom> getBody() const {
			return getRuleBody(Axiom(value));
		}
		Axiom getHead() const {
			return getRuleHead(Axiom(value));
		}
		int getImpulse(int dir) const {
			return impulse[dir];
		}
		int getSource(int i) const {
			return source[i];
		}
		std::string getType() const {
			return type;
		}
		std::string getValue() const {
			return value;
		}
		Axiom negate() {
			if (type == "PROP") {
				return Axiom("NOT(" + value + ")", source[0], source[1]);
			} else if (type == "NEG") {
				std::string v = value;
				v.erase(v.begin(), v.begin()+4);
				v.erase(v.end()-1, v.end());
				return Axiom(v);
			} else {
				return *this;
			}
		}
		void setImpulse(int n, int e, int s, int w) {
			impulse[0] = n;
			impulse[1] = e;
			impulse[2] = s;
			impulse[3] = w;
		}
		void setSource(int x, int y) {
			source[0] = x;
			source[1] = y;
		}
		void operator=(const Axiom& r) {
			value = r.value;
			type = getAxiomType(value);
			impulse[0] = r.impulse[0];
			impulse[1] = r.impulse[1];
			impulse[2] = r.impulse[2];
			impulse[3] = r.impulse[3];
			source[0] = r.source[0];
			source[1] = r.source[1];
		}
		friend bool operator==(const Axiom& l, const Axiom& r) {
			return l.value == r.value;
		}
		friend bool operator<(const Axiom& l, const Axiom& r) {
			return std::tie(l.type, l.value) < std::tie(r.type, r.value);
		}
	private:
		const std::string types[5] = {"BOUND","NEG","PROP","RULE","UNDEF"};
		std::string value;
		std::string type;
		int impulse[4];
		int source[2];
};

class Theory {
	public:
		Theory() {
			bBoundary = 0;
			axioms = std::set<Axiom>();
		}
		Theory(std::set<Axiom> a) {
			axioms = a;
			for (Axiom b : axioms) {
				if (b.getType() == "BOUND") {
					bBoundary = 1;
					break;
				}
			}
		}
		void addAxiom(Axiom a) {
			if (!bBoundary) {
				axioms.insert(a);
				if (a.getType() == "BOUND") {
					bBoundary = 1;
				}
			}
		}
		void fwdChaining() {
			std::set<Axiom> props = std::set<Axiom>();
			std::set<Axiom> rules = std::set<Axiom>();
			for (Axiom a : axioms) {
				if (a.getType() == "PROP" || a.getType() == "NEG") {
					props.insert(a);
				} else if (a.getType() == "RULE") {
					rules.insert(a);
				}
			}
			std::set<Axiom> body;
			Axiom head;
			bool infer;
			bool change;
			std::pair<std::set<Axiom>::iterator,bool> inserted;
			do {
				change = 0;
				for (Axiom r : rules) {
					body = r.getBody();
					infer = 1;
					for (Axiom b : body) {
						if (props.find(b) == props.end()) {
							infer = 0;
							break;
						}
					}
					if (infer) {
						head = r.getHead();
						if (head.getType() == "PROP" || head.getType() == "NEG") {
							addAxiom(head);
							inserted = props.insert(head);
							change = inserted.second;
						}
					}
				}
			} while (change);
		}
		bool is_boundary() const {
			return bBoundary;
		}
		bool is_inconsistent() const {
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
		std::set<Axiom> getAxiomSet() const {
			return axioms;
		}
		void removeAxiom(Axiom a) {
			axioms.erase(a);
		}
		friend bool operator==(const Theory& l, const Theory& r) { // might not be accurate
			return l.bBoundary == r.bBoundary && l.axioms == r.axioms;
		}
		friend bool operator!=(const Theory& l, const Theory& r) {
			return !(l == r);
		}
	private:
		bool bBoundary;
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
		grid[x][y].addAxiom(Axiom(prop, x, y));
	}
	
	File.close();
	
	std::cout << "\nInit:\n";
	printGrid(grid, n, m, "psi", "NOT(psi)");
	
	Theory newGrid[n][max_size];
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < m; j++) {
			newGrid[i][j] = grid[i][j];
		}
	}
	
	Axiom ax;
	std::set<Axiom> axioms;
	std::set<Axiom> neighborAxioms;
	std::queue<int> inconsistent;
	bool bContained;
	bool bChange;
	for (int k = 1; k <= steps; k++) {
		std::cout << "Step " << k << ":\n";
		for (int j = 1; j < m-1; j++) {
			for (int i = 1; i < n-1; i++) {
				if (grid[i][j].is_boundary()) {
					continue;
				}
				
				axioms = grid[i][j].getAxiomSet();
				for (Axiom a : axioms) {
					if (!newGrid[i+1][j].is_boundary() && a.getImpulse(1) > 0) {
						neighborAxioms = newGrid[i+1][j].getAxiomSet();
						ax = a;
						bContained = 0;
						for (Axiom b : neighborAxioms) {
							if (b == a) {
								newGrid[i+1][j].removeAxiom(b);
								if (b.getSource(0) == a.getSource(0) && b.getSource(1) == a.getSource(1)) {
									ax.decImpulse(3);
								} else {
									ax.setImpulse(1,1,1,1);
								}
								bContained = 1;
								break;
							}
						}
						if (!bContained) {
							ax.decImpulse(3);
						}
						newGrid[i+1][j].addAxiom(ax);
					}
					
					if (!newGrid[i-1][j].is_boundary() && a.getImpulse(3) > 0) {
						neighborAxioms = newGrid[i-1][j].getAxiomSet();
						ax = a;
						bContained = 0;
						for (Axiom b : neighborAxioms) {
							if (b == a) {
								newGrid[i-1][j].removeAxiom(b);
								if (b.getSource(0) == a.getSource(0) && b.getSource(1) == a.getSource(1)) {
									ax.decImpulse(1);
								} else {
									ax.setImpulse(1,1,1,1);
								}
								bContained = 1;
								break;
							}
						}
						if (!bContained) {
							ax.decImpulse(1);
						}
						newGrid[i-1][j].addAxiom(ax);
					}
					
					if (!newGrid[i][j+1].is_boundary() && a.getImpulse(0) > 0) {
						neighborAxioms = newGrid[i][j+1].getAxiomSet();
						ax = a;
						bContained = 0;
						for (Axiom b : neighborAxioms) {
							if (b == a) {
								newGrid[i][j+1].removeAxiom(b);
								if (b.getSource(0) == a.getSource(0) && b.getSource(1) == a.getSource(1)) {
									ax.decImpulse(2);
								} else {
									ax.setImpulse(1,1,1,1);
								}
								bContained = 1;
								break;
							}
						}
						if (!bContained) {
							ax.decImpulse(2);
						}
						newGrid[i][j+1].addAxiom(ax);
					}
					
					if (!newGrid[i][j-1].is_boundary() && a.getImpulse(2) > 0) {
						neighborAxioms = newGrid[i][j-1].getAxiomSet();
						ax = a;
						bContained = 0;
						for (Axiom b : neighborAxioms) {
							if (b == a) {
								newGrid[i][j-1].removeAxiom(b);
								if (b.getSource(0) == a.getSource(0) && b.getSource(1) == a.getSource(1)) {
									ax.decImpulse(0);
								} else {
									ax.setImpulse(1,1,1,1);
								}
								bContained = 1;
								break;
							}
						}
						if (!bContained) {
							ax.decImpulse(0);
						}
						newGrid[i][j-1].addAxiom(ax);
					}
					
					// decrease impulse
					ax = a;
					ax.decImpulse();
					newGrid[i][j].removeAxiom(a);
					newGrid[i][j].addAxiom(ax);
				}
			}
		}
		
		for (int j = 1; j < m-1; j++) {
			for (int i = 1; i < n-1; i++) {
				newGrid[i][j].fwdChaining();
				if (newGrid[i][j].is_inconsistent()) {
					newGrid[i][j] = Theory();
				}
			}
		}
		
		printGrid(newGrid, n, m, "psi", "NOT(psi)");
		
		/*for (int j = 1; j < m-1; j++) {
			for (int i = 1; i < n-1; i++) {
				axioms = newGrid[i][j].getAxiomSet();
				std::cout << "[INFO] (" << i << "," << j << ") ";
				for (Axiom a : axioms) {
					std::cout << a.getValue() << ":" << a.getImpulse(0) << "," << a.getImpulse(1) << "," << a.getImpulse(2) << "," << a.getImpulse(3) << "; ";
				}
				std::cout << " | " << newGrid[i][j].is_inconsistent();
				std::cout << std::endl;
			}
		}*/
		
		bChange = 0;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < m; j++) {
				if (grid[i][j] != newGrid[i][j]) {
					bChange = 1;
				}
				grid[i][j] = newGrid[i][j];
			}
		}
		if (!bChange) {
			break;
		}
	}
	
	/*Axiom rule = Axiom("phi:-psi,NOT(a)");
	std::set<Axiom> body = getRuleBody(rule);
	std::cout << "[INFO] Type: " << rule.getType() << ".\n";
	std::cout << "[INFO] Head: " << getRuleHead(rule) << ".\n";
	std::cout << "[INFO] Body: ";
	for (Axiom a : body) {
		std::cout << a.getValue() << " "; 
	}
	std::cout << std::endl;*/
	
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
	} 
	
	std::size_t found = value.find(":-", 0, 2);
	if (found != std::string::npos && found > 0) {
		return "RULE";
	} else if (value.find("()") == std::string::npos) {
		return "PROP";
	}
	
	return "UNDEF";
}

std::set<Axiom> getRuleBody(Axiom axiom) {
	if (axiom.getType() != "RULE") {
		return std::set<Axiom>();
	}
	std::string rule = axiom.getValue();
	std::size_t found = rule.find(":-", 0, 2);
	rule = rule.substr(found+2, std::string::npos);
	if (rule == "") {
		return std::set<Axiom>();
	}
	std::set<Axiom> body = std::set<Axiom>();
	Axiom prop;
	found = rule.find_last_of(",");
	while (found != std::string::npos) {
		prop = Axiom(rule.substr(found+1, std::string::npos));
		if (prop.getType() == "PROP" || prop.getType() == "NEG") {
			body.insert(prop);
		}
		rule = rule.erase(found, std::string::npos);
		found = rule.find_last_of(",");
	}
	prop = Axiom(rule);
	if (prop.getType() == "PROP" || prop.getType() == "NEG") {
			body.insert(prop);
	}
	return body;
}

Axiom getRuleHead(Axiom axiom) {
	if (axiom.getType() != "RULE") {
		return axiom.getValue();
	}
	std::string rule = axiom.getValue();
	std::size_t found = rule.find(":-", 0, 2);
	rule.erase(found, std::string::npos);
	return Axiom(rule);
}

void printGrid(Theory grid[][max_size], int n, int m, std::string v1, std::string v2) {
	std::set<Axiom> axioms;
	std::cout << std::endl;
	bool bContinue;
	for (int j = 0; j < m; j++) {
		for (int i = 0; i < n; i++) {
			axioms = grid[i][j].getAxiomSet();
			bContinue = 0;
			for (Axiom a : axioms) {
				if (a == boundary) {
					std::cout << "X ";
					bContinue = 1;
					break;
				} else if (a.getValue() == v1) {
					std::cout << "1 ";
					bContinue = 1;
					break;
				} else if (a.getValue() == v2) {
					std::cout << "2 ";
					bContinue = 1;
					break;
				}
			}
			if (!bContinue) {
				std::cout << "0 ";
			}
		}
		std::cout << std::endl;
	}
	std::cout << std:: endl;
}