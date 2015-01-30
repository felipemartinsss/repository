package util;

import java.util.ArrayList;

/**
 * Class used by ActionTransition.
 * ActionTransition uses a set of instances of ProbState
 * to represent the transition function P(.|s,a).
 * @author felipemartinsss and Mijail Gamarra Holguin.
 *
 */
public class ProbState implements Comparable {
	public double  _dProb;
	public ArrayList<Boolean> nextRepresentant;
	public ProbState(double Prob, ArrayList<Boolean> State) {
		_dProb = Prob;
		nextRepresentant = State;
	}
	public String toString(){
		return nextRepresentant.toString();
	} 

	public boolean equals( Object objeto ) {
		if (objeto == null || !(objeto instanceof ProbState) || !(objeto instanceof Double)) return false;
		double probaCompara = (objeto instanceof ProbState? ((ProbState)objeto)._dProb: (Double)objeto);
		return probaCompara == _dProb;
	} 

	public int hashCode() {
		return ((Double)_dProb).hashCode();
	} 

	public int compareTo( Object objeto ) {
		if (objeto == null || !(objeto instanceof ProbState) || !(objeto instanceof Double)) return -1;
		double probaCompara = (objeto instanceof ProbState? ((ProbState)objeto)._dProb: (Double)objeto);
		return ((Double)probaCompara).compareTo((Double)_dProb);
	}
}
