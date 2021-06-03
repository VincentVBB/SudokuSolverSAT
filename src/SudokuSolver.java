import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;

import stev.booleans.*;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;


public class SudokuSolver {

	public String sudoku = "";
	ArrayList<ArrayList<PropositionalVariable> > propositionalVarTab = new ArrayList<ArrayList<PropositionalVariable> >();


	public SudokuSolver(String sudoku) {
		this.sudoku = sudoku;
	}


	/* Creation des variables propositionnelles.
	 * Nous avons choisi de cr�e une liste comprennant des sous-listes.
	 * propositionalVarTab contient les 9 grilles des variables propositionnelles associ�es � chaques valeures (de 1 � 9).
	 * Une variable propositionnelle est cr�e ainsi : X, ligne, colonne, valeur
	 * La case de coordonn�e 1,3 avec la valeur 4 correspond donc � X,1,3,4
	 */
	public void create_var() {
		for (int val = 1; val<10; val++) {
			ArrayList<PropositionalVariable> propositionalVarTmp = new ArrayList<>();
			for (int row = 0; row<9; row++) {
				for (int col = 0; col<9;col++) {
					propositionalVarTmp.add(new PropositionalVariable("X"+row+","+col+","+val));
				}
			}
			propositionalVarTab.add(propositionalVarTmp);
		}
	}

	/* Chaque chiffre doit appara�tre exactement une fois dans chaque ligne de la grille
	 * R1 : Chaque chiffre doit apparaitre au moins une fois dans chaque ligne.
	 * R2 : Chaque chiffre doit apparaitre au plus une fois dans chaque ligne.
	 * R3 : R1 & R2
	 */
	public int[][] unSeulChiffre_ligne() {
		// R1 :
		And andR1 = new And();
		for (int row = 0; row < 9; row++ ) {
			And and = new And();
			for (int val = 1; val<10;val++) {
				Or or = new Or();
				for (int col = 0; col<9;col++) {
					or = new Or(or,this.propositionalVarTab.get(val-1).get(row*9+col));

				}
				and = new And(and, or);
			}
			andR1 = new And(andR1, and);
		}


		// R2 : 
		And andR2 = new And();
		for (int row = 0; row < 9; row++ ) {
			And andRow = new And();
			for (int val = 1; val<10;val++) {
				And andVal = new And();
				for (int col1 = 0; col1<9;col1++) {
					And andCol = new And();
					for (int col2 = 0; col2<9;col2++) {
						Or or = null;
						if(col1 != col2) {
							Not not1 = new Not(this.propositionalVarTab.get(val-1).get(row*9+col1));
							Not not2 = new Not(this.propositionalVarTab.get(val-1).get(row*9+col2));
							or = new Or(not1, not2);
						}
						if(or !=null ) {
							andCol = new And(andCol, or);
						}
					}
					if(andCol !=null) {
						andVal = new And(andVal,andCol);
					}
				}
				if(andVal!=null) {
					andRow = new And(andRow, andVal);
				}
			}
			if(andRow!=null) {
				andR2 = new And(andR2,andRow);
			}	
		}

		// R3 :

		And andR3 = new And(andR1, andR2);


		BooleanFormula cnf = BooleanFormula.toCnf(andR3);
		return cnf.getClauses();
	}


	/* Chaque case doit avoir exactement un seul chiffre de 1 � 9
	 * K1 : Chaque case doit avoir au moins un chiffre.
	 * K2 : Chaque case doit avoir au plus un chiffre.
	 * K3 : K1 & K2
	 */
	public int[][] unSeulChiffre_case() {
		// K1 :
		And andK1 = new And();
		for (int row = 0; row < 9; row++ ) {
			And and = new And();
			for (int col = 0; col<9;col++) {
				Or or = new Or();
				for (int val = 1; val<10;val++) {
					or = new Or(or,this.propositionalVarTab.get(val-1).get(row*9+col));

				}
				and = new And(and, or);
			}
			andK1 = new And(andK1, and);
		}


		// K2 : 
		And andK2 = new And();
		for (int row = 0; row < 9; row++ ) {
			And andRow = new And();
			for (int col = 0; col<9;col++) {
				And andCol = new And();
				for (int val1 = 1; val1<9;val1++) {
					And andVal = new And();
					for (int val2 = val1+1; val2<10;val2++) {
						Or or = null;
						Not not1 = new Not(this.propositionalVarTab.get(val1-1).get(row*9+col));
						Not not2 = new Not(this.propositionalVarTab.get(val2-1).get(row*9+col));
						or = new Or(not1, not2);

						andVal = new And(andVal, or);

					}
					andCol = new And(andCol,andVal);

				}
				andRow = new And(andRow, andCol);

			}
			andK2 = new And(andK2,andRow);

		}

		// R3 :

		And andK3 = new And(andK1, andK2);


		BooleanFormula cnf = BooleanFormula.toCnf(andK3);
		return cnf.getClauses();
	}


	/* Chaque chiffre doit appara�tre exactement une fois dans chaque colonne de la grille
	 * C1 : Chaque chiffre doit apparaitre au moins une fois dans chaque colonne.
	 * C2 : Chaque chiffre doit apparaitre au plus une fois dans chaque colonne.
	 * C3 : C1 & C2
	 */
	public int[][] unSeulChiffre_colonne() {
		// C1 :
		And andC1 = new And();
		for (int col = 0; col < 9; col++ ) {
			And and = new And();
			for (int val = 1; val<10;val++) {
				Or or = new Or();
				for (int row = 0; row<9;row++) {
					or = new Or(or,this.propositionalVarTab.get(val-1).get(row*9+col));
				}
				and = new And(and, or);
			}
			andC1 = new And(andC1, and);
		}


		// C2 : 
		And andC2 = new And();
		for (int col = 0; col<9;col++) {
			And andCol = new And();
			for (int val = 1; val<10;val++) {
				And andVal = new And();
				for (int row1 = 0; row1<8;row1++) {
					And andRow = new And();
					for (int row2 = row1+1; row2<9;row2++) {
						Or or = null;
						Not not1 = new Not(this.propositionalVarTab.get(val-1).get(row1*9+col));
						Not not2 = new Not(this.propositionalVarTab.get(val-1).get(row2*9+col));
						or = new Or(not1, not2);

						andRow = new And(andRow, or);

					}
					andVal = new And(andVal,andRow);

				}
				andCol = new And(andCol,andVal);

			}
			andC2 = new And(andC2,andCol);

		}

		// C3 :

		And andC3 = new And(andC1, andC2);


		BooleanFormula cnf = BooleanFormula.toCnf(andC3);
		return cnf.getClauses();
	}

	/**
	 * On initialise une pile vide de clause puis on parcourt le tableau. 
	 * Si l’on trouve une valeur k != 0 dans la case(i, j), on ajoute à la pile les clauses xi,j,k et  ¬xi,j,q pour tout q!=k
	 * (attention: une clause unitaire est une liste de longueur 1)
	 * @param grilleDepart
	 * @return
	 */
	public int[][] grilleDepartToClause(String[][] grilleDepart) {
		int [][] clauses = null;
		And andBegin = new And();
		for(int row =0; row<9; row++) {
			And andRow = new And();
			for(int col=0; col<9; col++) {
				And andCol = new And();
				for(int val=1; val<10; val++) {
					And andVal = new And();
					if(grilleDepart[row][col].equals(String.valueOf(val))) {
						for(int val2=1; val2<10; val2++) {
							And and=null;
							if(val!=val2) {
								Not not = new Not(this.propositionalVarTab.get(val2-1).get(row*9+col));
								and = new And(this.propositionalVarTab.get(val-1).get(row*9+col), not);
							}
							if(and!=null)
							andVal= new And (andVal, and);
						}
					}
					andCol = new And(andCol, andVal);
				}
				andRow = new And(andRow, andCol);
			}
			andBegin = new And (andBegin, andRow);
		}
		BooleanFormula cnf = BooleanFormula.toCnf(andBegin);
		return cnf.getClauses();
	}




	public static void main(String[] args)
	{
		String grilleSudoku = 
				  "#26###81#"
				+ "3##7#8##6"
				+ "4###5###7"
				+ "#5#1#7#9#"
				+ "##39#51##"
				+ "#4#3#2#5#"
				+ "1###3###2"
				+ "5##2#4##9"
				+ "#38###46#";
		String[][] grilleDepart = {
				{"#","2","6","#","#","#","8","1","#"},
				{"3","#","#","7","#","8","#","#","6"},
				{"4","#","#","#","5","#","#","#","7"},
				{"#","5","#","1","#","7","#","9","#"},
				{"#","#","3","9","#","5","1","#","#"},
				{"#","4","#","3","#","2","#","5","#"},
				{"1","#","#","#","3","#","#","#","2"},
				{"5","#","#","2","#","4","#","#","9"},
				{"#","3","8","#","#","#","4","6","#"},			
		};

		SudokuSolver su = new SudokuSolver(grilleSudoku);
		su.create_var();
		int[][] unseulChiffre_ligne = su.unSeulChiffre_ligne();		
		int[][] unseulChiffre_case = su.unSeulChiffre_case();		
		int[][] unseulChiffre_colonne = su.unSeulChiffre_colonne();		
		int[][] conditionInitiales = su.grilleDepartToClause(grilleDepart);


		for(int c = 0; c < conditionInitiales.length; c++) {
			System.out.println(Arrays.toString(conditionInitiales[c]));
		}
		/*
		 * System.out.println();
		ISolver solver = SolverFactory.newDefault();


		for(int c = 0; c < clauses.length; c++) {
			System.out.println(Arrays.toString(clauses[c]));
			try {
				solver.addClause(new VecInt(clauses[c]));
			} catch (ContradictionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

		}

		return true;
		 */
	}
}
