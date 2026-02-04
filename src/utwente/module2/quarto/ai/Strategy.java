package utwente.module2.quarto.ai;

import utwente.module2.quarto.gamelogic.Game;
import utwente.module2.quarto.gamelogic.Move;
import utwente.module2.quarto.gamelogic.Piece;

/**
 * Interface representing a strategy for a computer player in Quarto.
 * Defines how to select a move on the board and how to choose a piece for the opponent.
 */
public interface Strategy {

    /**
     * Returns the name of this strategy.
     * @return the strategy name
     */
    String getName();

    /**
     * Determines the next move (placement of the current piece) given the current game state.
     * @param game the current game
     * @return a valid move according to this strategy
     */
    Move determineMove(Game game);

    /**
     * Determines which piece to give to the opponent.
     * @param game the current game
     * @return the selected piece
     */
    Piece determinePiece(Game game);
}