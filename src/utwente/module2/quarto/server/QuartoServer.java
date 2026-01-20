package utwente.module2.quarto.server;

import utwente.module2.quarto.networking.Packet;
import utwente.module2.quarto.networking.Protocol;

import java.io.IOException;
import java.net.Socket;
import java.util.*;

/**
 * The main server class for the Quarto game.
 * It manages connections and initializes the game server.
 */
public class QuartoServer extends SocketServer {

    // All connected clients
    private final List<ClientHandler> clients = new ArrayList<>();

    // Waiting queues. Key = Lobby Name Value = Client waiting.
    private final Map<String, ClientHandler> queues = new HashMap<>();

    // Active games. Key = Client Value = The GameSession.
    private final Map<ClientHandler, GameSession> activeGames = new HashMap<>();

    // Lobbies where a game is currently in progress.
    private final Set<String> activeLobbies = new HashSet<>();


    /**
     * Constructs a new QuartoServer on the given port.
     * @param port the port to listen on.
     * @throws IOException if the server socket cannot be opened.
     */
    public QuartoServer(int port) throws IOException {
        super(port);
    }

    /**
     * The entry point of the server application.
     * Prompts the user for a port and starts the server.
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
     * Handles a new incoming connection.
     * Creates a ClientHandler for the connection and starts receiving messages.
     * @param socket the socket for the new connection.
     */
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

    public synchronized void addClient(ClientHandler client) {
        clients.add(client);
        System.out.println("[SERVER] User logged in: " + client.getUsername());
    }

    public synchronized void removeClient(ClientHandler client) {
        clients.remove(client);
        queues.values().remove(client);

        GameSession session = activeGames.get(client);
        if (session != null) {
            session.playerDisconnected(client);
            activeGames.remove(client);
        }

        System.out.println("[SERVER] User disconnected: " + client.getUsername());
    }

    public synchronized boolean isUsernameTaken(String name) {
        for (ClientHandler client : clients) {
            if (name.equals(client.getUsername())) {
                return true;
            }
        }
        return false;
    }

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
     * Handles a client request to join a queue (Lobby).
     * @param client The client requesting.
     * @param lobbyName The name of the lobby (e.g., "Lobby1"). Empty string for default.
     */
    public synchronized void handleQueueCommand(ClientHandler client, String lobbyName) {
        // 1. If trying to join a lobby where a game is already playing
        if (activeLobbies.contains(lobbyName)) {
            System.out.println("Game in process, could not connect");
        }

        // 2. If client is already in THIS queue -> remove (toggle behavior)
        if (queues.containsKey(lobbyName) && queues.get(lobbyName) == client) {
            queues.remove(lobbyName);
            System.out.println(client.getUsername() + " left queue: " + lobbyName);
            return;
        }

        // 3. Remove client from ANY other queue they might be in
        queues.values().remove(client);

        // 4. Check if someone is waiting in this lobby
        if (queues.containsKey(lobbyName)) {
            ClientHandler opponent = queues.get(lobbyName);
            queues.remove(lobbyName);

            System.out.println("Match found in " + lobbyName + ": " + client.getUsername() + " vs " + opponent.getUsername());

            // Mark lobby as active (playing)
            if (!lobbyName.isEmpty()) {
                activeLobbies.add(lobbyName);
            }

            startNewGame(client, opponent, lobbyName);

        } else {
            // No one waiting, put this client in queue
            queues.put(lobbyName, client);
            System.out.println(client.getUsername() + " joined queue: " + lobbyName);
        }
    }

    private void startNewGame(ClientHandler player1, ClientHandler player2, String lobbyName) {
        GameSession session = new GameSession(player1, player2, lobbyName);
        activeGames.put(player1, session);
        activeGames.put(player2, session);
    }

    public void handleMove(ClientHandler player, Packet packet) {
        GameSession session = activeGames.get(player);
        if (session != null) {
            session.handleMove(player, packet);
        } else {

        }
    }

    /**
     * Called by GameSession when a game ends.
     * Frees up the lobby so others can see it
     */
    public synchronized void onGameEnded(String lobbyName, ClientHandler p1, ClientHandler p2) {
        if (lobbyName != null && !lobbyName.isEmpty()) {
            activeLobbies.remove(lobbyName);
        }
        activeGames.remove(p1);
        activeGames.remove(p2);
    }

    /**
     * Returns a string representing the status of lobbies.
     * Format: LobbyName:WaitingCount:IsPlaying
     * Example: "Lobby1:1:false~Lobby2:0:true"
     */
    public synchronized String getLobbyStats() {
        StringBuilder stats = new StringBuilder();

        for (int i = 1; i <= 5; i++) {
            String name = "Lobby #" + i;

            int waiting = queues.containsKey(name) ? 1 : 0;
            boolean isPlaying = activeLobbies.contains(name);

            if (i > 1) stats.append(Protocol.DELIMITER);
            stats.append(name)
                    .append(":").append(waiting)
                    .append(":").append(isPlaying);
        }
        return stats.toString();
    }

}