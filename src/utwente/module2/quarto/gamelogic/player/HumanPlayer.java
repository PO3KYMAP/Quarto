package utwente.module2.quarto.gamelogic.player;

import java.util.List;
import java.util.Scanner;
import utwente.module2.quarto.gamelogic.*;

/**
 * HumanPlayer represents a player that provides moves via console input.
 */
public class HumanPlayer extends AbstractPlayer {

    /**
     * Creates a human player with the given name.
     *
     * @param name the name of the player
     */
    /*@
      @ requires name != null;
      @ ensures getName().equals(name);
      @*/
    public HumanPlayer(String name) {
        super(name);
    }

    /**
     * Determines the next move by asking the user for input.
     *
     * @param game the current game instance
     * @return a valid Move chosen by the human player
     */
    /*@
      @ requires game != null;
      @ ensures game.isValidMove(\result);
      @*/
    @Override
    public Move determineMove(Game game) {
        QuartoGame qGame = (QuartoGame) game;

        if (qGame.getCurrentPiece() == null) {
            throw new IllegalStateException("No piece to place");
        }

        Piece currentPiece = qGame.getCurrentPiece();
        Scanner input = new Scanner(System.in);
        QuartoMove move;
        int pos;

        do {
            System.out.print(getName() + ", enter a position (0-15): ");

            while (!input.hasNextInt()) {
                System.out.println("Please enter a number between 0 and 15.");
                input.next();
            }

            pos = input.nextInt();
            move = new QuartoMove(currentPiece, pos);

            if (!game.isValidMove(move)) {
                System.out.println("Invalid move. Try again.");
            }

        } while (!game.isValidMove(move));

        return move;
    }

    @Override
    public Piece determinePiece(Game game) {
        QuartoGame qGame = (QuartoGame) game;
        Scanner input = new Scanner(System.in);

        Piece chosen = null;

        do {
            System.out.println("Available pieces:");
            List<Piece> available = qGame.getAvailablePieces();
            printAvailablePieces(qGame, available);

            System.out.print(getName() + ", choose a piece for your opponent (0-" + (available.size()-1) + "): ");

            while (!input.hasNextInt()) {
                System.out.println("Please enter a valid number.");
                input.next(); // discard invalid input
            }

            int index = input.nextInt();

            if (index >= 0 && index < available.size()) {
                chosen = available.get(index);
            } else {
                System.out.println("Invalid choice. Try again.");
            }
        } while (chosen == null);

        return chosen;
    }
    public void printAvailablePieces(Game game,List<Piece> pieces) {
        for (int i = 0; i < pieces.size(); i++) {
            System.out.printf("%2d:%s  ", i, pieces.get(i));
            if ((i+1) % 4 == 0) System.out.println();
        }
        System.out.println();
    }
}
