package utwente.module2.quarto.gamelogic;

import java.util.Scanner;
import java.util.List;
import utwente.module2.quarto.gamelogic.*;
import utwente.module2.quarto.gamelogic.player.*;

/**
 * Text-based User Interface (TUI) for Quarto.
 */
public class QuartoTUI {

    private QuartoGame game;

    public QuartoTUI() {
        // setup two human players for now
        Scanner input = new Scanner(System.in);
        System.out.print("Enter name for Player 1: ");
        String name1 = input.nextLine();
        System.out.print("Enter name for Player 2: ");
        String name2 = input.nextLine();

        Player p1 = new HumanPlayer(name1);
        Player p2 = new HumanPlayer(name2);

        this.game = new QuartoGame(p1, p2);
    }

    public static void main(String[] args) {
        QuartoTUI tui = new QuartoTUI();
        tui.run();
    }

    public void run() {
        Scanner input = new Scanner(System.in);

        while (!game.isGameover()) {
            System.out.println(game.board); // print current board
            Player currentPlayer = game.getTurn();
            System.out.println("It's " + currentPlayer.getName() + "'s turn.");
            Piece currentPiece = game.getCurrentPiece();

            if (currentPiece == null) {
                // choose a piece for the opponent
                Piece chosen = ((HumanPlayer) currentPlayer).determinePiece(game);
                game.choosePiece(chosen);
            } else {
                // place the current piece
                System.out.println("Current piece: " + currentPiece);
                Move move = ((HumanPlayer) currentPlayer).determineMove(game);
                game.doMove(move);
            }
        }

        System.out.println(game.board);
        if (game.getWinner() != null) {
            System.out.println("Winner: " + game.getWinner().getName());
        } else {
            System.out.println("Draw! No winner.");
        }
    }
}
