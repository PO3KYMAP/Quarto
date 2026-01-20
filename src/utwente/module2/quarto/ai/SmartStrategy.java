package utwente.module2.quarto.ai;

import utwente.module2.quarto.ai.Strategy;
import utwente.module2.quarto.gamelogic.*;

/**
 * A smarter AI strategy that tries to win or block the opponent's winning move.
 * If no immediate win or threat is present, it selects a random valid move.
 */
public class SmartStrategy implements Strategy {

    /**
     * Returns the name of the strategy.
     *
     * @return "Smart"
     */
    /*@
      @ ensures \result.equals("Smart");
      @*/
    @Override
    public String getName() {
        return "Smart";
    }

    /**
     * Determines the next move using the following logic in order:
     * 1. If a winning move is available, take it.
     * 2. If the opponent has a winning move next, block it.
     * 3. Otherwise, choose a random valid move.
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
        QuartoGame qGame = (QuartoGame) game;
        QuartoMove move;
        int pos;

        // Determine the current mark


        // Check if there is a winning move for this player
        Move WinningMove = isWinningMove(qGame);
        if (WinningMove != null) {
            return WinningMove;
        }

//        // Check if enemy has a winning move to block
//        int EnemyWinningIndex = isWinningMoveEnemy(qGame);
//        if (EnemyWinningIndex != -1) {
//            return new QuartoMove(currentMark, EnemyWinningIndex);
//        }
//
//        // Otherwise, pick a random valid move
//        do {
//            pos = (int)(Math.random() * 9);
//            move = new QuartoMove(currentMark, pos);
//        } while (!game.isValidMove(move));

        return null;
    }

    /**
     * Checks if there is a move that would win the game for the current player.
     *
     * @param game the current game state
     * @return a winning Move if available, otherwise null
     */
    /*@
      @ requires game != null;
      @*/
    public Move isWinningMove(QuartoGame game) {
        for (Move i : game.getValidMoves()) {
            Game temp = new QuartoGame(game); // Copy current game
            temp.doMove(i); // Simulate move
            if (temp.getWinner() == game.getTurn()) {
                return i; // Return winning move
            }
        }
        return null;
    }

    /**
     * Checks if the opponent has a winning move that should be blocked.
     *
     * @param game the current game state
     * @return the index to block, or -1 if no threat exists
     */
    /*@
      @ requires game != null;
      @*/
    public int isWinningMoveEnemy(QuartoGame game) {
        for (Move i : game.getValidMoves()) {
            Game temp = new QuartoGame(game); // Copy current game
            temp.doMove(i); // Simulate move
            Move WinningMove = isWinningMove((QuartoGame) temp);
            if (WinningMove != null) {
                return WinningMove.getIndex(); // Return index to block
            }
        }
        return -1; // No immediate threat
    }
}
