package utwente.module2.quarto.ai;

import utwente.module2.quarto.gamelogic.*;
import java.util.List;
import java.util.Random;

/**
 * A simple AI strategy that chooses moves and pieces randomly.
 * Useful for testing or easy difficulty.
 */
public class NaiveStrategy implements Strategy {

    private final Random random = new Random();

    /*@ ensures \result.equals("Naive"); @*/
    @Override
    public String getName() {
        return "Naive";
    }

    /**
     * Selects a random valid position on the board.
     * @param game the current game state
     * @return a valid QuartoMove
     */
    /*@ requires game != null;
        ensures game.isValidMove(\result);
    @*/
    @Override
    public Move determineMove(Game game) {
        QuartoGame qGame = (QuartoGame) game;
        Piece piece = qGame.getCurrentPiece();

        if (piece == null) return null; // Should not happen in correct flow

        Move move;
        do {
            int pos = random.nextInt(16); // 0..15
            move = new QuartoMove(piece, pos);
        } while (!game.isValidMove(move));

        return move;
    }

    /**
     * Selects a random available piece.
     * @param game the current game state
     * @return a piece from the available list
     */
    /*@ requires game != null;
        ensures \result != null;
    @*/
    @Override
    public Piece determinePiece(Game game) {
        QuartoGame qGame = (QuartoGame) game;
        List<Piece> available = qGame.getAvailablePieces();

        if (available.isEmpty()) return null;

        return available.get(random.nextInt(available.size()));
    }
}