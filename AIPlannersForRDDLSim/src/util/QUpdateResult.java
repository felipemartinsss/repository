package util;

import java.util.ArrayList;

/**
 * Classe that wraps a Q Value computed by LRTDP.
 * @author felipemartinsss and Mijail Gamarra Holguin.
 *
 */
public class QUpdateResult {
	public CString _csBestAction;
	public double  _dBestQValue;
	public ArrayList<ProbState> _alProbEstados;
	public QUpdateResult(CString best_action, double best_qvalue, ArrayList<ProbState> ProbEstados) {
		_csBestAction = best_action;
		_dBestQValue  = best_qvalue;
		_alProbEstados = ProbEstados;
	}
}
