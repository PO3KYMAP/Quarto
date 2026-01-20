package utwente.module2.quarto.gamelogic;

import java.util.List;
import utwente.module2.quarto.gamelogic.player.Player;

/**
 * A simple turn-based game.
 */
public interface Game {
    //@ instance invariant !isGameover() ==> getValidMoves().size() > 0;
    //@ instance invariant !isGameover() ==> getWinner() == null;
    //@ instance invariant !isGameover() ==> getTurn() != null;

    /**
     * Check if the game is over, i.e., there is a winner or no more moves are available.
     * @return whether the game is over
     */
    //@ pure;
    boolean isGameover();

    /**
     * Query whose turn it is
     * @return the player whose turn it is
     */
    //@ pure;
    Player getTurn();

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     * @return the winner, or null if no player is the winner or the game is not over
     */
    //@ pure;
    Player getWinner();

    /**
     * Return all moves that are valid in the current state of the game
     * @return the list of currently valid moves
     */
    //@ ensures (\forall Move m; \result.contains(m); isValidMove(m));
    //@ pure;
    List<? extends Move> getValidMoves();

    /**
     * Check if a move is a valid move
     * @param move the move to check
     * @return true if the move is a valid move
     */
    //@ ensures \result <==> (\exists Move m; getValidMoves().contains(m); m.equals(move));
    //@ pure;
    boolean isValidMove(Move move);

    /**
     * Perform the move, assuming it is a valid move.
     * @param move the move to play
     */
    //@ requires isValidMove(move);
    void doMove(Move move);
}
