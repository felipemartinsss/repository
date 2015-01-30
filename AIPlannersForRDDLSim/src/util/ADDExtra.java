package util;

import dd.discrete.ADD;
import dd.discrete.ADDINode;
import dd.discrete.ADDNode;

public class ADDExtra {

	private ADD _context;
	
	public ADDExtra(ADD _context) {
		this._context = _context;
	}
	
	/**
	 * Devolve a altura de um nó do ADD baseado no conceito de altura para arvores binarias.
	 * @param node
	 * @return
	 */
	public int getNodeHeight (ADDNode node) {
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				ADDNode highSon = _context.getNode(internalNode._nHigh);
				ADDNode lowSon = _context.getNode(internalNode._nLow);
				int highSonHeight = getNodeHeight (highSon);
				int lowSonHeight = getNodeHeight (lowSon);
				if (highSonHeight < lowSonHeight) {
					return lowSonHeight + 1;
				} else {
					return highSonHeight + 1;
				}
			} else {
				return 0;
			}
		} else {
			return -1;
		}
	}
	
}
