package utwente.module2.quarto.server;

import utwente.module2.quarto.networking.Connection;
import utwente.module2.quarto.networking.Packet;
import utwente.module2.quarto.networking.Protocol;

import java.io.IOException;
import java.net.Socket;

/**
 * Handles the communication with a single client.
 */
public class ClientHandler extends Connection {

    private final QuartoServer server;
    private String username;
    private boolean helloExchanged = false;

    /**
     * Creates a new ClientHandler.
     * @param socket the socket for this connection.
     * @param server reference to the main server.
     */
    public ClientHandler(Socket socket, QuartoServer server) throws IOException {
        super(socket);
        this.server = server;
    }

    /**
     * Called when the connection starts.
     */
    @Override
    protected void handleStart() {
        System.out.println("Connection started.");
    }

    /**
     * Called when a message is received from the client.
     */
    @Override
    protected void handleMessage(String message) {
        Packet packet = new Packet(message);
        String command = packet.getCommand();

        System.out.println("Received command: " + command);

        switch (command) {
            case Protocol.HELLO -> handleHello(packet);
            case Protocol.LOGIN -> handleLogin(packet);
            case Protocol.QUEUE -> handleQueue(packet);
            case Protocol.LIST -> handleList();
            case Protocol.MOVE -> handleMove(packet);
            case Protocol.LOBBY_STATS -> handleLobbyStats();
            default -> sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Unknown command");
        }

    }

    private void handleHello(Packet packet) {
        if (helloExchanged) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Handshake already done");
            return;
        }

        sendMessage(Protocol.HELLO + Protocol.DELIMITER + "QuartoServer");
        helloExchanged = true;
    }

    private void handleLogin(Packet packet) {
        if (!helloExchanged) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Handshake missing");
            return;
        }

        if (packet.getArgCount() < 1) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Missing username");
            return;
        }

        if (this.username != null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Already logged in");
            return;
        }

        String requestedName = packet.getArg(0);

        if (server.isUsernameTaken(requestedName)) {
            sendMessage(Protocol.ALREADYLOGGEDIN);
        } else {
            this.username = requestedName;
            server.addClient(this);
            sendMessage(Protocol.LOGIN);
        }
    }

    private void handleQueue(Packet packet) {
        if (username == null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not logged in");
            return;
        }

        String lobbyName = "";
        if (packet.getArgCount() > 0) {
            lobbyName = packet.getArg(0);
        }

        server.handleQueueCommand(this, lobbyName);
    }

    private void handleList() {
        if (username == null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not logged in");
            return;
        }

        String listString = server.getPlayerListString();
        sendMessage(Protocol.LIST + Protocol.DELIMITER + listString);
    }

    private void handleLobbyStats() {
        if (username == null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not logged in");
            return;
        }
        String stats = server.getLobbyStats();
        sendMessage(Protocol.LOBBY_STATS + Protocol.DELIMITER + stats);
    }

    public QuartoServer getServer() {
        return server;
    }

    private void handleMove(Packet packet) {
        if (username == null) {
            sendMessage(Protocol.ERROR + Protocol.DELIMITER + "Not logged in");
            return;
        }

        server.handleMove(this, packet);
    }
    /**
     * Called when the client disconnects.
     */
    @Override
    protected void handleDisconnect() {
        System.out.println("Client disconnected: " + (username != null ? username : "Unknown"));
        server.removeClient(this);
    }

    /**
     * @return the username of this client (or null if not logged in)
     */
    public String getUsername() {
        return username;
    }
}