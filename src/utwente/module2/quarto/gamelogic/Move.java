package utwente.module2.quarto.gamelogic;

/**
 * A move in a turn-based game.
 * A move typically consists of a mark (player identity)
 * and an index indicating where the move is applied.
 */
public interface Move {


    /**
     * Returns the index at which this move is played.
     * The meaning of the index depends on the game implementation.
     *
     * @return the index of the move
     */
    public int getIndex();
}
