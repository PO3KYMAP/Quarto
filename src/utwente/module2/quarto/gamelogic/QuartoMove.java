package utwente.module2.quarto.gamelogic;

/**
 * Represents a move in Quarto: placing a specific piece on a board position.
 */
public class QuartoMove implements Move {

    private final Piece piece;
    private final int index;

    /**
     * Creates a new Quarto move.
     *
     * @param piece the piece to place
     * @param index the board position (0–15)
     * @throws IllegalArgumentException if piece is null or index invalid
     */
    public QuartoMove(Piece piece, int index) {
        if (piece == null) {
            throw new IllegalArgumentException("Piece cannot be null");
        }
        if (index < 0 || index >= Board.DIM * Board.DIM) {
            throw new IllegalArgumentException("Invalid index: " + index);
        }
        this.piece = piece;
        this.index = index;
    }

    public Piece getPiece() {
        return piece;
    }

    @Override
    public int getIndex() {
        return index;
    }
}
