package utwente.module2.quarto.gamelogic;


/**
 * Board for the game.
 */
public class Board {
    /**
     * Dimension of the board, i.e., if set to 3, the board has 3 rows and 3 columns.
     */
    public static final int DIM = 4;
    private Piece[] fields;


    /**
     * The DIM by DIM fields of the Tic-Tac-Toe board. See NUMBERING for the
     * coding of the fields.
     */

    // -- Constructors -----------------------------------------------
    /**
     * Creates an empty board.
     */
    public Board() {
        fields = new Piece[DIM * DIM];
    }

    /**
     * Creates a deep copy of this field.
     */
    public Board deepCopy() {
    	 Board copy = new Board();
         for (int i = 0; isField(i); i++) {
             copy.fields[i] = this.fields[i];
         }
         return copy;
    }

    /**
     * Calculates the index in the linear array of fields from a (row, col)
     * pair.
     * @return the index belonging to the (row,col)-field
     */
    public int index(int row, int col) {
        return row * DIM + col;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     * @return true if 0 <= index < DIM*DIM
     */
    //@ ensures index >= 0 && index < DIM*DIM ==> \result == true;
    public boolean isField(int index) {
         return (0 <= index && index < DIM*DIM);
    }

    /**
     * Returns true of the (row,col) pair refers to a valid field on the board.
     * @return true if 0 <= row < DIM && 0 <= col < DIM
     */
    //@ ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
    public boolean isField(int row, int col) {
         return row >= 0 && row < DIM && col >= 0 && col < DIM;
    }

    /**
     * Returns the content of the field i.
     * @param i the number of the field (see NUMBERING)
     * @return the mark on the field
     */
    public Piece getField(int i) {
    	 if(isField(i)) {
             return fields[i];
         }
         return null;
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     * @param row the row of the field
     * @param col the column of the field
     * @return the mark on the field
     */
    public Piece getField(int row, int col) {
    	 if(isField(row, col)) {
             int i = index(row, col);
             return fields[i];
         }
         return null;
    }

    /**
     * Returns true if the field 'i' is empty.
     * @param i the index of the field (see NUMBERING)
     * @return true if the field is empty
     */
    public boolean isEmptyField(int i) {
    	 return getField(i) == null;
    }

    /**
     * Returns true if the field referred to by the (row,col) pair is empty.
     * @param row the row of the field
     * @param col the column of the field
     * @return true if the field is empty
     */
    public boolean isEmptyField(int row, int col) {
        return (getField(row, col) == null);
    }

    /**
     * Tests if the whole board is full.
     * @return true if all fields are occupied
     */
    public boolean isFull() {
        for (int i = 0; isField(i); i++) {
            if (fields[i] == null) {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     * @return true if the game is over
     */
    public boolean gameOver() {
         return (hasWinner() || isFull());
    }


    private boolean allPresent(Piece[] pieces) {
        for (Piece p : pieces) {
            if (p == null) return false;
        }
        return true;
    }

    private boolean sharesColor(Piece[] p) {
        Color color = p[0].getColor();
        for (int i = 1; i < DIM; i++) {
            if (p[i].getColor() != color) return false;
        }
        return true;
    }

    private boolean sharesSize(Piece[] p) {
        Size size = p[0].getSize();
        for (int i = 1; i < DIM; i++) {
            if (p[i].getSize() != size) return false;
        }
        return true;
    }

    private boolean sharesShape(Piece[] p) {
        Shape shape = p[0].getShape();
        for (int i = 1; i < DIM; i++) {
            if (p[i].getShape() != shape) return false;
        }
        return true;
    }

    private boolean sharesFill(Piece[] p) {
        Fill fill = p[0].getFill();
        for (int i = 1; i < DIM; i++) {
            if (p[i].getFill() != fill) return false;
        }
        return true;
    }

    private boolean sharesAnyAttribute(Piece[] pieces) {
        if (!allPresent(pieces)) return false;

        return sharesColor(pieces)
                || sharesSize(pieces)
                || sharesShape(pieces)
                || sharesFill(pieces);
    }

    public boolean hasQuartoRow(int row) {
        Piece[] pieces = new Piece[DIM];
        for (int col = 0; col < DIM; col++) {
            pieces[col] = getField(row, col);
        }
        return sharesAnyAttribute(pieces);
    }

    public boolean hasQuartoColumn(int col) {
        Piece[] pieces = new Piece[DIM];
        for (int row = 0; row < DIM; row++) {
            pieces[row] = getField(row, col);
        }
        return sharesAnyAttribute(pieces);
    }

    public boolean hasQuartoDiagonal() {
        Piece[] diag1 = new Piece[DIM];
        Piece[] diag2 = new Piece[DIM];

        for (int i = 0; i < DIM; i++) {
            diag1[i] = getField(i, i);
            diag2[i] = getField(i, DIM - 1 - i);
        }

        return sharesAnyAttribute(diag1) || sharesAnyAttribute(diag2);
    }

    public boolean hasWinner() {
        for (int i = 0; i < DIM; i++) {
            if (hasQuartoRow(i) || hasQuartoColumn(i)) {
                return true;
            }
        }
        return hasQuartoDiagonal();
    }

    public void setField(int index, Piece piece) {
        if (!isField(index)) {
            throw new IllegalArgumentException("Invalid index");
        }
        fields[index] = piece;
    }

    public void setField(int row, int col, Piece piece) {
        int index = index(row, col);
        if (!isField(index)) {
            throw new IllegalArgumentException("Invalid index");
        }
        fields[index] = piece;
    }

    public void reset() {
        for (int i = 0; isField(i); i++) {
            fields[i] = null;
        }
    }
    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        int cellWidth = 5; // fixed width for each cell

        // Top border
        sb.append("┌─────┬─────┬─────┬─────┐\n");

        for (int row = 0; row < DIM; row++) {
            sb.append("│"); // start of row
            for (int col = 0; col < DIM; col++) {
                Piece p = getField(row, col);
                String content;
                if (p == null) {
                    // show index, centered
                    String indexStr = String.valueOf(index(row, col));
                    int pad = (cellWidth - indexStr.length()) / 2;
                    content = " ".repeat(pad) + indexStr + " ".repeat(cellWidth - indexStr.length() - pad);
                } else {
                    // show piece string, centered
                    String s = p.toString();
                    int pad = (cellWidth - s.length()) / 2;
                    content = " ".repeat(pad) + s + " ".repeat(cellWidth - s.length() - pad);
                }
                sb.append(content).append("│");
            }
            sb.append("\n");

            // Row separators
            if (row < DIM - 1) {
                sb.append("├─────┼─────┼─────┼─────┤\n");
            } else {
                sb.append("└─────┴─────┴─────┴─────┘\n");
            }
        }

        return sb.toString();
    }
}
