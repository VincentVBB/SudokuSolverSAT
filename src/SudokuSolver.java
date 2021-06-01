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
	public ArrayList<PropositionalVariable> propositionalVar = new ArrayList<>();
	

	public SudokuSolver(String sudoku) {
		super();
		this.sudoku = sudoku;
	}



	public void create_var() {
		for (int x = 0; x<9; x++) {
			for (int y = 0; y<9; y++) {
				for (int val = 1; val<10;val++) {
					propositionalVar.add(new PropositionalVariable("X"+x+","+y+","+val));
				}
			}
		}
	}
	
	
	public Boolean unSeulChiffre(String line) {
		ArrayList<PropositionalVariable> propositionalVarLine = new ArrayList<>();
		for (int y = 0; y<9; y++) {
			for (int val = 1; val<10;val++) {
				propositionalVarLine.add(new PropositionalVariable("X : "+y+","+val));
			}
		}
		Or or = new Or();
		And and = new And();
		for (int k = 0; k<9;k++) {
			for (int y = k; y<9-k;y++) {
				or = new Or(or,propositionalVarLine.get(y));
			
			}
			and = new And(and, or);
		}
		System.out.println(and);
		
		BooleanFormula cnf = BooleanFormula.toCnf(and);
		System.out.println();
		System.out.println(cnf);
		
		int[][] clauses = cnf.getClauses();
		System.out.println();
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
	}
	
	
	public ArrayList<PropositionalVariable> getPropositionalVar() {
		return propositionalVar;
	}



	public void setPropositionalVar(ArrayList<PropositionalVariable> propositionalVar) {
		this.propositionalVar = propositionalVar;
	}
	
	
	public static void main(String[] args)
	{
		String test = "#26###81#";
		
		
		SudokuSolver su = new SudokuSolver(test);
		su.create_var();
		su.unSeulChiffre(test);		
		
		
	}
}
