package utwente.module2.quarto.ai;

import utwente.module2.quarto.client.NetworkListener;
import utwente.module2.quarto.client.QuartoClient;
import utwente.module2.quarto.gamelogic.Move;
import utwente.module2.quarto.gamelogic.Piece;
import utwente.module2.quarto.gamelogic.QuartoGame;
import utwente.module2.quarto.gamelogic.QuartoMove;
import utwente.module2.quarto.gamelogic.player.HumanPlayer;
import utwente.module2.quarto.gamelogic.player.Player;

import java.io.IOException;
import java.net.InetAddress;
import java.util.List;
import java.util.Scanner;

/**
 * A client application that connects to a Quarto server and plays the game automatically using an AI strategy.
 */
public class AIClient implements NetworkListener {

    private final QuartoClient client;
    private final ComputerPlayer player;
    private final String name;
    private QuartoGame localGame;
    private Player myPlayer;
    private Integer lastSentIndex = null;
    private Integer lastSentPieceId = null;
    private Piece pieceGivenToOpponent = null;

    public AIClient(String name, Strategy strategy, String host, int port) throws IOException {
        this.name = name;
        this.player = new ComputerPlayer(strategy);
        this.client = new QuartoClient(InetAddress.getByName(host), port, this);
    }

    public void start() {
        client.start();
        client.login(name);
        client.queue();
    }

    @Override
    public void onConnected() {
        System.out.println("[AI] Connected to server.");
    }

    @Override
    public void onGameStarted(String opponent, boolean iAmStarting) {
        System.out.println("[AI] Game started vs " + opponent);

        Player p1, p2;
        if (iAmStarting) {
            p1 = new HumanPlayer(name);
            p2 = new HumanPlayer(opponent);
            myPlayer = p1;
        } else {
            p1 = new HumanPlayer(opponent);
            p2 = new HumanPlayer(name);
            myPlayer = p2;
        }

        localGame = new QuartoGame(p1, p2);
        lastSentIndex = null;
        lastSentPieceId = null;
        pieceGivenToOpponent = null;

        if (iAmStarting) {
            System.out.println("[AI] I am starting. Choosing first piece...");
            Piece p = player.determinePiece(localGame);
            if (p != null) {
                localGame.choosePiece(p);
                lastSentIndex = -1;
                lastSentPieceId = p.toProtocolId();
                pieceGivenToOpponent = p;
                client.sendMove(-1, p.toProtocolId());
            }
        }
    }

    @Override
    public void onMoveReceived(int index, int pieceId) {
        if (lastSentIndex != null && lastSentPieceId != null) {
            if (lastSentIndex == index && lastSentPieceId == pieceId) {
                lastSentIndex = null;
                lastSentPieceId = null;
                return;
            }
        }

        if (pieceId == 16 || pieceId == 17) {
            if (index != -1) {
                Piece pieceThatWasPlaced = pieceGivenToOpponent;
                if (pieceThatWasPlaced == null && localGame != null) {
                    pieceThatWasPlaced = localGame.getCurrentPiece();
                }
                if (pieceThatWasPlaced != null && localGame != null && localGame.getBoard().isEmptyField(index)) {
                    localGame.doMove(new QuartoMove(pieceThatWasPlaced, index));
                }
            }
            pieceGivenToOpponent = null;
            return;
        }

        Piece pieceReceived = Piece.fromProtocolId(pieceId);

        // 3. Обработка хода соперника
        if (index == -1 && pieceReceived != null) {
            if (localGame.getCurrentPiece() == null) {
                localGame.choosePiece(pieceReceived);
            }
        } else if (index != -1) {
            Piece pieceThatWasPlaced = pieceGivenToOpponent;
            if (pieceThatWasPlaced == null && localGame != null) {
                pieceThatWasPlaced = localGame.getCurrentPiece();
            }

            System.out.println("[AI] Opponent moved: index=" + index + ", giving pieceId=" + pieceId);

            if (localGame != null && pieceThatWasPlaced != null && localGame.getBoard().isEmptyField(index)) {
                localGame.doMove(new QuartoMove(pieceThatWasPlaced, index));

                if (localGame.isGameover()) {
                    System.out.println("[AI] Opponent missed the win! Claiming victory now.");
                    int freeIndex = -1;
                    for (int i = 0; i < 16; i++) {
                        if (localGame.getBoard().isEmptyField(i)) {
                            freeIndex = i;
                            break;
                        }
                    }
                    if (freeIndex != -1) {
                        System.out.println("[AI] Punishing opponent: Place at " + freeIndex + " (16)");
                        client.sendMove(freeIndex, 16);
                        pieceGivenToOpponent = null;
                        lastSentIndex = freeIndex;
                        lastSentPieceId = 16;
                        return;
                    }
                }
            } else {
                System.err.println("[AI] WARNING: Cannot place piece at " + index);
            }

            pieceGivenToOpponent = null;

            if (localGame != null && !localGame.isGameover()) {
                if (pieceReceived != null && localGame.getCurrentPiece() == null) {
                    localGame.choosePiece(pieceReceived);
                }
            }
        }

        if (localGame == null) return;

        if (!localGame.isGameover() && isMyTurn()) {
            try {

                Thread.sleep(100);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }

        if (!localGame.isGameover() && isMyTurn()) {
            try {
                if (localGame.getCurrentPiece() != null) {
                    Move move = player.determineMove(localGame);

                    if (move == null) {
                        System.err.println("[AI] No valid move found!");
                        return;
                    }

                    QuartoGame tempForWinCheck = new QuartoGame(localGame);
                    tempForWinCheck.doMove(move);
                    boolean isWinningMove = tempForWinCheck.isGameover() && tempForWinCheck.getWinner() != null;

                    if (isWinningMove) {
                        pieceGivenToOpponent = null;
                        localGame.doMove(move);
                        lastSentIndex = move.getIndex();
                        lastSentPieceId = 16;
                        System.out.println("[AI] 🏆 VICTORY! Claiming win at " + move.getIndex());
                        client.sendMove(move.getIndex(), 16);
                        return;
                    }

                    QuartoGame tempForNextPiece = new QuartoGame(localGame);
                    tempForNextPiece.doMove(move);

                    List<Piece> remaining = tempForNextPiece.getAvailablePieces();

                    if (remaining.isEmpty()) {
                        pieceGivenToOpponent = null;
                        localGame.doMove(move);
                        lastSentIndex = move.getIndex();
                        lastSentPieceId = 17;
                        System.out.println("[AI] Last move at " + move.getIndex() + " (17)");
                        client.sendMove(move.getIndex(), 17);
                    } else {
                        Piece nextPiece = player.determinePiece(tempForNextPiece);

                        if (nextPiece == null) nextPiece = remaining.get(0);

                        pieceGivenToOpponent = nextPiece;
                        localGame.doMove(move); // Теперь делаем ход в реальной игре
                        if (!localGame.isGameover()) {
                            localGame.choosePiece(nextPiece);
                        }

                        lastSentIndex = move.getIndex();
                        lastSentPieceId = nextPiece.toProtocolId();
                        System.out.println("[AI] Moving: Place " + move.getIndex() + ", Give " + lastSentPieceId);
                        client.sendMove(move.getIndex(), lastSentPieceId);
                    }

                } else {
                    Piece firstPiece = player.determinePiece(localGame);
                    if (firstPiece != null) {
                        localGame.choosePiece(firstPiece);
                        lastSentIndex = -1;
                        lastSentPieceId = firstPiece.toProtocolId();
                        pieceGivenToOpponent = firstPiece;
                        System.out.println("[AI] Choosing first piece: " + lastSentPieceId);
                        client.sendMove(-1, lastSentPieceId);
                    }
                }
            } catch (Exception e) {
                System.err.println("[AI Error] " + e.getMessage());
                e.printStackTrace();
            }
        }
    }

    private boolean isMyTurn() {
        return localGame.getTurn().getName().equals(name);
    }

    @Override
    public void onGameOver(String reason, String winner) {
        System.out.println("[AI] ========== GAMEOVER RECEIVED ==========");
        System.out.println("[AI] Reason: " + reason + ", Winner: " + winner);
        localGame = null;
        myPlayer = null;
        lastSentIndex = null;
        lastSentPieceId = null;
        pieceGivenToOpponent = null;
        try { Thread.sleep(100); } catch (InterruptedException e) {}
        System.out.println("[AI] Queuing for next game...");
        client.queue();
    }

    @Override
    public void onError(String error) {
        System.err.println("[AI Error] " + error);
        if (error.contains("already taken")) System.exit(1);
    }

    @Override public void onLoginSuccess() {}
    @Override public void onListReceived(String list) {}

    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        System.out.println("═══ AI CLIENT LAUNCHER ═══");
        System.out.print("Server Port: ");
        int port = -1;
        while (port <= 0) {
            if (scanner.hasNextInt()) {
                port = scanner.nextInt();
                scanner.nextLine();
            } else {
                System.out.print("Invalid port. Try again: ");
                scanner.next();
            }
        }

        System.out.print("Bot Name [Enter for random]: ");
        String inputName = scanner.nextLine().trim();
        String name = inputName.isEmpty() ? "Bot_" + (int) (Math.random() * 1000) : inputName;

        System.out.print("Strategy (n = Naive, s = Smart) [Default: Smart]: ");
        String stratInput = scanner.nextLine().trim().toLowerCase();
        Strategy strat;
        if (stratInput.startsWith("n")) strat = new NaiveStrategy();
        else strat = new SmartStrategy();

        System.out.print("Enter server host: ");
        String inputHost = scanner.nextLine().trim();
        try {
            System.out.println("------------------------------------------------");
            System.out.println("Launching " + name + " (" + strat.getName() + ") -> port " + port);
            System.out.println("------------------------------------------------");
            new AIClient(name, strat, inputHost, port).start();
        } catch (IOException e) {
            System.err.println("Connection failed: " + e.getMessage());
        }
    }
}