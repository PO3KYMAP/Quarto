package utwente.module2.quarto.ai;

import utwente.module2.quarto.gamelogic.*;
import java.util.List;
import java.util.Random;

/**
 * A smarter AI strategy.
 * 1. Placement phase: Takes a winning move immediately if available.
 * 2. Selection phase: Avoids giving the opponent a piece they can win with.
 */
public class SmartStrategy implements Strategy {

    private final Random random = new Random();

    /*@ ensures \result.equals("Smart"); @*/
    @Override
    public String getName() {
        return "Smart";
    }

    /**
     * Determines the move. Priority: Win > Random.
     * @param game the current game state
     * @return a winning move or a random valid move
     */
    /*@ requires game != null;
        ensures game.isValidMove(\result);
    @*/
    @Override
    public Move determineMove(Game game) {
        QuartoGame qGame = (QuartoGame) game;

        // 1. Try to win immediately
        Move winningMove = findWinningMove(qGame);
        if (winningMove != null) {
            return winningMove;
        }

        // 2. Random valid move otherwise
        List<? extends Move> validMoves = qGame.getValidMoves();

        if (validMoves.isEmpty()) return null;

        return validMoves.get(random.nextInt(validMoves.size()));
    }

    /**
     * Determines the piece to give. Priority: Safe piece > Random.
     * A "safe" piece is one that the opponent cannot use to win on their next turn.
     * @param game the current game state
     * @return a safe piece or a random one if all are dangerous
     */
    /*@ requires game != null;
        ensures \result != null;
    @*/
    @Override
    public Piece determinePiece(Game game) {
        QuartoGame qGame = (QuartoGame) game;
        List<Piece> available = qGame.getAvailablePieces();

        if (available.isEmpty()) {
            return null;
        }

        for (Piece piece : available) {
            if (isSafeToGive(qGame, piece)) {
                return piece;
            }
        }

        return available.get(random.nextInt(available.size()));
    }

    /**
     * Helper method to find a winning move in the current game state.
     * Simulates every valid move on a copy of the game board.
     *
     * @param game the current game state.
     * @return the {@link Move} that results in a win, or {@code null} if no such move exists.
     */
    private Move findWinningMove(QuartoGame game) {
        for (Move move : game.getValidMoves()) {
            QuartoGame copy = new QuartoGame(game);
            copy.doMove(move);
            if (copy.isGameover() && copy.getWinner() != null) {
                return move;
            }
        }
        return null;
    }

    /**
     * Helper method to determine if a specific piece is safe to give to the opponent.
     * <p>
     * It simulates giving the piece to the opponent and then checks if the opponent
     * has any valid move that results in a win.
     *
     * @param originalGame the current game state.
     * @param pieceToCheck the piece to evaluate.
     * @return {@code true} if the opponent cannot win immediately with this piece; {@code false} otherwise.
     */
    private boolean isSafeToGive(QuartoGame originalGame, Piece pieceToCheck) {
        QuartoGame simGame = new QuartoGame(originalGame);

        simGame.setCurrentPiece(pieceToCheck);

        for (Move move : simGame.getValidMoves()) {
            QuartoGame innerCopy = new QuartoGame(simGame);
            innerCopy.doMove(move);
            if (innerCopy.isGameover() && innerCopy.getWinner() != null) {
                return false;
            }
        }
        return true;
    }
}