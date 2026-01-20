package utwente.module2.quarto.ai;

import utwente.module2.quarto.gamelogic.Game;
import utwente.module2.quarto.gamelogic.Move;

/**
 * Interface representing a strategy for selecting a move in a Tic-Tac-Toe game.
 */
public interface Strategy {

    /**
     * Returns the name of this strategy.
     * @return the strategy name
     */
    //@ ensures \result != null;
    public String getName();

    /**
     * Determines the next move given the current game state.
     * @param game the current game
     * @return a legal move according to this strategy
     */
    //@ requires game != null;
    //@ ensures \result != null;
    public Move determineMove(Game game);
}
