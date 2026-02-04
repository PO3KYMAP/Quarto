package utwente.module2.quarto.ai;

import utwente.module2.quarto.gamelogic.Game;
import utwente.module2.quarto.gamelogic.Move;
import utwente.module2.quarto.gamelogic.Piece;
import utwente.module2.quarto.gamelogic.player.AbstractPlayer;

/**
 * Represents a computer-controlled player.
 * Delegates decision-making to a provided Strategy.
 */
public class ComputerPlayer extends AbstractPlayer {

    private /*@ spec_public @*/ Strategy strategy;

    /**
     * Creates a computer player with the given strategy.
     * @param strategy the strategy to determine moves
     */
    /*@ requires strategy != null;
        ensures getStrategy() == strategy;
    @*/
    public ComputerPlayer(Strategy strategy) {
        super(strategy.getName());
        this.strategy = strategy;
    }

    /**
     * Determines the next move using the assigned strategy.
     * @param game the current game
     * @return the move chosen by the strategy
     */
    /*@ requires game != null;
        ensures \result != null;
    @*/
    @Override
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }

    /**
     * Determines the piece to give to the opponent using the assigned strategy.
     * @param game the current game
     * @return the piece chosen by the strategy
     */
    /*@ requires game != null;
        ensures \result != null;
    @*/
    @Override
    public Piece determinePiece(Game game) {
        return strategy.determinePiece(game);
    }

    /**
     * Returns the current strategy.
     * @return the strategy
     */
    /*@
        ensures \result == strategy;
        pure;
    @*/
    public Strategy getStrategy() {
        return strategy;
    }

    /**
     * Sets a new strategy for the player.
     * @param strategy the new strategy
     */
    /*@ requires strategy != null;
        ensures getStrategy() == strategy;
    @*/
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }
}