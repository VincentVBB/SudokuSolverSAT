import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;

import stev.booleans.*;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;




/*
 * @author Nicolas_Kerneis (KERN08049808), Nesrine_Chekou(CHEN04619700), David_Lhullier(LHUD14029704 ), Vincent Vanbalberghe(VANV20019704)
 */
public class SudokuSolver {
	
	ArrayList<PropositionalVariable> propositionalVarAll = new ArrayList<PropositionalVariable>();
	ArrayList<ArrayList<PropositionalVariable> > propositionalVarTab = new ArrayList<ArrayList<PropositionalVariable> >(); //Pour les 3 premières règles
	ArrayList<ArrayList<ArrayList<PropositionalVariable>> > propositionalVarBloc = new ArrayList<ArrayList<ArrayList<PropositionalVariable>>>(); //Pour la règle sur les blocs


	/* Creation des variables propositionnelles.
	 * Nous avons choisi de cree une liste comprennant des sous-listes.
	 * propositionalVarTab contient les 9 grilles des variables propositionnelles associees a chaques valeures (de 1 � 9).
	 * propositionalVarBloc contient les 9 blocs ranger par valeurs.
	 * propositionnalVarAll contient toutes les variables propositionnelle dans l'odre ligne, colonne, valeur
	 * Une variable propositionnelle est cree ainsi : X, ligne, colonne, valeur correspondant a la case de coordonnee i,j contient la valeur k
	 * La case de coordonnee 1,3 avec la valeur 4 correspond donc a X,1,3,4
	 */
	public void create_var() {
		for (int val = 1; val<10; val++) {
			ArrayList<PropositionalVariable> propositionalVarTmp = new ArrayList<>();
			for (int row = 0; row<9; row++) {
				for (int col = 0; col<9;col++) {
					propositionalVarTmp.add(new PropositionalVariable("X,"+row+","+col+","+val));
				}
			}
			propositionalVarTab.add(propositionalVarTmp);
		}
		for (int row = 0; row<9; row++) {
			for (int col = 0; col<9; col++) {
				for (int val = 1; val<10;val++) {
					propositionalVarAll.add(new PropositionalVariable("X,"+row+","+col+","+val));
				}
			}
		}

		for(int val =1; val<10; val++) {
			ArrayList<ArrayList<PropositionalVariable>> propositionalVarTmp = new ArrayList<>();
			for (int row = 0; row<9; row+=3) {
				for (int col = 0; col<9;col+=3) {
					ArrayList<PropositionalVariable> propositionalVarTmpBis = new ArrayList<>();
					int _i = row-(row%3), _j = col-(col%3);
					for(int x=_i;x<_i+3; x++) {
						for(int y=_j;y<_j+3; y++) {
							propositionalVarTmpBis.add(new PropositionalVariable("X,"+x+","+y+","+val));
						}
					}
					propositionalVarTmp.add(propositionalVarTmpBis);
				}
				propositionalVarBloc.add(propositionalVarTmp);
			}
		}
	}

	/* Chaque chiffre doit apparaitre exactement une fois dans chaque ligne de la grille
	 * R1 : Chaque chiffre doit apparaitre au moins une fois dans chaque ligne.
	 * R2 : Chaque chiffre doit apparaitre au plus une fois dans chaque ligne.
	 * R3 = R1 & R2
	 */
	public BooleanFormula unSeulChiffre_ligne() {
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
		return cnf;
	}


	/* K3 :Chaque case doit avoir exactement un seul chiffre de 1 � 9
	 * K1 : Chaque case doit avoir au moins un chiffre.
	 * K2 : Chaque case doit avoir au plus un chiffre.
	 * K3 = K1 & K2
	 */
	public BooleanFormula unSeulChiffre_case() {
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
		return cnf;
	}


	/* C3 :Chaque chiffre doit appara�tre exactement une fois dans chaque colonne de la grille
	 * C1 : Chaque chiffre doit apparaitre au moins une fois dans chaque colonne.
	 * C2 : Chaque chiffre doit apparaitre au plus une fois dans chaque colonne.
	 * C3 = C1 & C2
	 */
	public BooleanFormula unSeulChiffre_colonne() {
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
		return cnf;
	}


	/*
	 * D3 : Chaque chiffre doit appara�tre exactement une fois dans chaque bloc de la grille
	 * D1 : Chaque chiffre doit apparaitre au moins une fois dans chaque bloc.
	 * D2 : Chaque chiffre doit apparaitre au plus une fois dans chaque bloc.
	 * D3 = D1 & D2
	 */
	public BooleanFormula unSeulChiffre_bloc() {
		//D1
		And andD1 = new And();
		for (int bloc =0; bloc<9; bloc++) {
			And andBloc = new And();
			for(int val =1; val<10; val++) {
				Or or = new Or();
				for(int indice =0; indice<9; indice++) {
					or = new Or(or,this.propositionalVarBloc.get(val-1).get(bloc).get(indice));
				}
				andBloc = new And(andBloc, or);
			}
			andD1 = new And(andD1, andBloc);
		}

		//D2
		And andD2 = new And();
		for (int bloc = 0; bloc<9;bloc++) {
			And andBloc = new And();
			for (int val = 1; val<10;val++) {
				And andVal = new And();
				for (int indice1 = 0; indice1<8;indice1++) {
					And andIndice1 = new And();
					for (int indice2 = indice1+1; indice2<9;indice2++) {
						Or or = null;
						Not not1 = new Not(this.propositionalVarBloc.get(val-1).get(bloc).get(indice1));
						Not not2 = new Not(this.propositionalVarBloc.get(val-1).get(bloc).get(indice2));
						or = new Or(not1, not2);
						andIndice1 = new And(andIndice1, or);
					}
					andVal = new And(andVal,andIndice1);
				}
				andBloc = new And(andBloc,andVal);
			}
			andD2 = new And(andD2,andBloc);
		}
		//D3
		And andD3 = new And(andD1, andD2);
		BooleanFormula cnf = BooleanFormula.toCnf(andD3);
		return cnf;
	}




	/**
	 * On initialise une pile vide de clause puis on parcourt le tableau. 
	 * Si l’on trouve une valeur k != 0 dans la case(i, j), on ajoute à la pile les clauses xi,j,k et  ¬xi,j,q pour tout q!=k
	 */
	public BooleanFormula grilleDepartToClause(String[][] grilleDepart) {
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
		return cnf;
	}




	public static void main(String[] args) throws TimeoutException
	{
		//Recuperation de la grille initiale de sudoku
		String sudoku = args[0];
		
		//Transformation en matrice String[][]
		String[][] grilleDepart=new String [9][9];
		char[] sudokuTab = sudoku.toCharArray();
		int ligne=0;
		for(int i =0; i<sudokuTab.length; i+=9) {
			String[] sudokuLineTmp = new String[9];
			for(int j=0; j<9; j++) {
				sudokuLineTmp[j]=Character.toString(sudokuTab[j+i]);
			}
			grilleDepart[ligne]=sudokuLineTmp;
			ligne++;
		}
		
		System.out.println("Grille de départ : ");
		for(int i=0; i<9; i++) {
			System.out.println();
			for(int j=0; j<9; j++) {
				System.out.print(grilleDepart[i][j]);
			}
		}
		System.out.println();

		SudokuSolver su = new SudokuSolver();
		//Creation des variables propositionnelles
		su.create_var();

		//Creation des CNF associées aux règles du sudoku
		BooleanFormula unseulChiffre_case = su.unSeulChiffre_case();		
		BooleanFormula unseulChiffre_ligne = su.unSeulChiffre_ligne();		
		BooleanFormula unseulChiffre_colonne = su.unSeulChiffre_colonne();		
		BooleanFormula unseulChiffre_bloc = su.unSeulChiffre_bloc();

		//Creation des CNF associées au sudoku initial
		BooleanFormula conditionInitiales = su.grilleDepartToClause(grilleDepart);
		
		//Creation du la formule de logique propositionnelle respectant toutes les règles du sudoku et la grille de départ
		And and = new And(unseulChiffre_case, unseulChiffre_ligne, unseulChiffre_colonne, unseulChiffre_bloc, conditionInitiales);
		BooleanFormula finalCnf = BooleanFormula.toCnf(and);
		
		//Recuperation des clauses
		int[][] clauses = finalCnf.getClauses();
		Map<String,Integer> associations = finalCnf.getVariablesMap();

		//Creation du solver
		ISolver solver = SolverFactory.newDefault();

		//Ajout des clauses au solver
		for(int c = 0; c < clauses.length; c++) {
			try {
				solver.addClause(new VecInt(clauses[c]));
			} catch (ContradictionException e) {
				e.printStackTrace();
			}
		}
		
		//Reponse : problème solvable ou non
		IProblem problem = solver;
		if (problem.isSatisfiable()) { 
			for(int i=1; i<730; i++) {
				if(problem.model(i)) { //recuperer les variables qui sont dans la grille de sudoku valide
					String variable = su.propositionalVarAll.get(i-1).toString();
					String[] infoVariable = variable.split(",");
					grilleDepart[Integer.parseInt(infoVariable[1])][Integer.parseInt(infoVariable[2])] = infoVariable[3];
				}
			}

			System.out.println("on a une solution au problème");
			for(int i=0; i<9; i++) {
				System.out.println();
				for(int j =0; j<9; j++) {
					System.out.print(grilleDepart[i][j]); //Affiche la grille resolue
				}
			}
		} else {
			System.out.println("Il n'existe pas de solution");
		}
	}
}