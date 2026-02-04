package utwente.module2.quarto.server;

import utwente.module2.quarto.networking.Packet;
import utwente.module2.quarto.networking.Protocol;

import java.io.IOException;
import java.net.Socket;
import java.util.*;

/**
 * The main server class for the Quarto game.
 * Manages client connections, a single matchmaking queue, and active game sessions.
 * Clients join the queue via QUEUE; when two are waiting, a game starts automatically.
 */
public class QuartoServer extends SocketServer {

    /*@ private invariant clients != null;
        private invariant matchmakingQueue != null;
        private invariant activeGames != null;
    @*/

    private final List<ClientHandler> clients = new ArrayList<>();
    private final List<ClientHandler> matchmakingQueue = new ArrayList<>();
    private final Map<ClientHandler, GameSession> activeGames = new HashMap<>();

    /**
     * Constructs a new QuartoServer listening on the specified port.
     *
     * @param port the port number to listen on.
     * @throws IOException if an I/O error occurs when opening the socket.
     */
    /*@ requires port >= 0;
    @*/
    public QuartoServer(int port) throws IOException {
        super(port);
    }

    /**
     * The entry point of the server application.
     * Configures the port and starts listening for connections.
     *
     * @param args command line arguments.
     */
    public static void main(String[] args) {
        System.out.println("Enter port number (0 for automatic):");
        Scanner sc = new Scanner(System.in);
        int port = 0;

        if (sc.hasNextInt()) {
            port = sc.nextInt();
        } else {
            System.out.println("Invalid input, using default (0).");
        }

        try {
            QuartoServer server = new QuartoServer(port);
            System.out.println("Server started on port: " + server.getPort());
            server.acceptConnections();
        } catch (IOException e) {
            System.err.println("Could not start server: " + e.getMessage());
        }
    }

    /**
     * Accepts a new client connection and initializes a handler for it.
     *
     * @param socket the client socket.
     */
    /*@ requires socket != null;
    @*/
    @Override
    protected void handleConnection(Socket socket) {
        try {
            ClientHandler handler = new ClientHandler(socket, this);
            handler.start();
            System.out.println("New connection from: " + socket.getInetAddress());
        } catch (IOException e) {
            System.err.println("Error creating ClientHandler: " + e.getMessage());
            try {
                socket.close();
            } catch (IOException ignored) {}
        }
    }

    /**
     * Registers a logged-in client.
     *
     * @param client the client handler to add.
     */
    /*@ requires client != null;
        ensures clients.contains(client);
    @*/
    public synchronized void addClient(ClientHandler client) {
        clients.add(client);
        System.out.println("[SERVER] User logged in: " + client.getUsername());
    }

    /**
     * Removes a client from the server, cleaning up queues and active games.
     *
     * @param client the client handler to remove.
     */
    /*@ requires client != null;
        ensures !clients.contains(client);
    @*/
    public synchronized void removeClient(ClientHandler client) {
        clients.remove(client);
        matchmakingQueue.remove(client);

        GameSession session = activeGames.get(client);
        if (session != null) {
            session.playerDisconnected(client);
            activeGames.remove(client);

            ClientHandler opponent = (client == session.getPlayer1()) ? session.getPlayer2() : session.getPlayer1();
            if (opponent != null && activeGames.containsKey(opponent)) {
                activeGames.remove(opponent);
            }
        }

        System.out.println("[SERVER] User disconnected: " + client.getUsername());
    }

    /**
     * Checks if a username is already currently in use.
     *
     * @param name the username to check.
     * @return true if the username is taken, false otherwise.
     */
    /*@ requires name != null;
        pure
    @*/
    public synchronized boolean isUsernameTaken(String name) {
        for (ClientHandler client : clients) {
            if (name.equals(client.getUsername())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Generates a delimited string of all connected usernames.
     *
     * @return a string containing all usernames separated by the protocol delimiter.
     */
    /*@ pure @*/
    public synchronized String getPlayerListString() {
        List<String> names = new ArrayList<>();
        for (ClientHandler client : clients) {
            if (client.getUsername() != null) {
                names.add(client.getUsername());
            }
        }
        return String.join(Protocol.DELIMITER, names);
    }

    /**
     * Processes a client's request to join or leave the matchmaking queue.
     * Sending QUEUE again removes the client from the queue.
     * When two clients are waiting, a game is started automatically.
     *
     * @param client the client requesting to queue or leave.
     */
    /*@ requires client != null;
    @*/
    public synchronized void handleQueueCommand(ClientHandler client) {
        if (matchmakingQueue.contains(client)) {
            matchmakingQueue.remove(client);
            System.out.println(client.getUsername() + " left queue");
            return;
        }

        matchmakingQueue.add(client);
        System.out.println(client.getUsername() + " joined queue");

        if (matchmakingQueue.size() >= 2) {
            ClientHandler player1 = matchmakingQueue.remove(0);
            ClientHandler player2 = matchmakingQueue.remove(0);
            System.out.println("Match found: " + player1.getUsername() + " vs " + player2.getUsername());
            startNewGame(player1, player2);
        }
    }

    /**
     * Starts a new game session between two players.
     *
     * @param player1 the first player.
     * @param player2 the second player.
     */
    /*@ requires player1 != null && player2 != null;
        ensures activeGames.containsKey(player1) && activeGames.containsKey(player2);
    @*/
    private void startNewGame(ClientHandler player1, ClientHandler player2) {
        GameSession session = new GameSession(player1, player2);
        activeGames.put(player1, session);
        activeGames.put(player2, session);
    }

    /**
     * Routes a move packet to the appropriate game session.
     *
     * @param player the player making the move.
     * @param packet the move packet.
     */
    /*@ requires player != null && packet != null;
    @*/
    public synchronized void handleMove(ClientHandler player, Packet packet) {
        GameSession session = activeGames.get(player);
        if (session != null) {
            session.handleMove(player, packet);
        }
    }

    /**
     * Callback method called when a game session ends.
     * Cleans up active game references so both players can queue again.
     *
     * @param p1 the first player.
     * @param p2 the second player.
     */
    /*@ requires p1 != null && p2 != null;
    @*/
    public synchronized void onGameEnded(ClientHandler p1, ClientHandler p2) {
        activeGames.remove(p1);
        activeGames.remove(p2);
        System.out.println("Game ended. Players " + p1.getUsername() + " and " + p2.getUsername() + " are free.");
    }
}