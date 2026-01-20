package utwente.module2.quarto.ai;

import utwente.module2.quarto.ai.Strategy;
import utwente.module2.quarto.gamelogic.*;

/**
 * A simple AI strategy that chooses moves randomly from available positions.
 */
public class NaiveStrategy implements Strategy {

    /**
     * Returns the name of the strategy.
     *
     * @return "Naive"
     */
    /*@
      @ ensures \result.equals("Naive");
      @*/
    @Override
    public String getName() {
        return "Naive";
    }

    /**
     * Determines a move by selecting a random empty position on the board.
     *
     * @param game the current game state
     * @return a valid QuartoMove
     */
    /*@
      @ requires game != null;
      @ ensures game.isValidMove(\result);
      @*/
    @Override
    public Move determineMove(Game game) {
        // Cast the generic Game to QuartoGame
        QuartoGame qGame = (QuartoGame) game;

        QuartoMove move;
        int pos;

        // Determine the current mark
        

//        // Keep picking random positions until a valid move is found
//        do {
//            pos = (int)(Math.random() * 9); // random index 0-8
//            move = new QuartoMove(piece, pos);
//        } while (!game.isValidMove(move));

        return null;
    }
}
