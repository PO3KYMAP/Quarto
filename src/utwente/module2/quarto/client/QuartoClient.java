package utwente.module2.quarto.client;

import utwente.module2.quarto.networking.Connection;
import utwente.module2.quarto.networking.Packet;
import utwente.module2.quarto.networking.Protocol;

import java.io.IOException;
import java.net.InetAddress;
import java.util.ArrayList;
import java.util.List;

public class QuartoClient extends Connection {

    private final List<NetworkListener> listeners = new ArrayList<>();
    private String myName;


    public QuartoClient(InetAddress host, int port, NetworkListener listener) throws IOException {
        super(host, port);
        addListener(listener);
    }

    public void addListener(NetworkListener listener) {
        listeners.add(listener);
    }

    public String getMyName() {
        return myName;
    }

    public void login(String username) {
        this.myName = username;
        sendMessage(Protocol.HELLO + Protocol.DELIMITER + "JavaClient by Vadim");
        sendMessage(Protocol.LOGIN + Protocol.DELIMITER + username);
    }

    public void joinLobby(String lobbyName) {
        if (lobbyName == null) lobbyName = "";
        sendMessage(Protocol.QUEUE + Protocol.DELIMITER + lobbyName);
    }

    public void requestList() {
        sendMessage(Protocol.LIST);
    }

    public void requestLobbyStats() {
        sendMessage(Protocol.LOBBY_STATS);
    }

    public void sendMove(int index, int pieceId) {
        if (index == -1) {
            sendMessage(Protocol.MOVE + Protocol.DELIMITER + pieceId);
        } else {
            sendMessage(Protocol.MOVE + Protocol.DELIMITER + index + Protocol.DELIMITER + pieceId);
        }
    }



    @Override
    protected void handleMessage(String message) {
        Packet packet = new Packet(message);
        String cmd = packet.getCommand();

        // System.out.println("DEBUG (Client got): " + message);

        switch (cmd) {
            case Protocol.HELLO:
                for (NetworkListener l : listeners) l.onConnected();
                break;

            case Protocol.LOGIN:
                break;

            case Protocol.ALREADYLOGGEDIN:
                for (NetworkListener l : listeners) l.onError("Username already taken!");
                break;

            case Protocol.NEWGAME:
                if (packet.getArgCount() >= 2) {
                    String p1 = packet.getArg(0);
                    String p2 = packet.getArg(1);
                    String opponent = p1.equals(myName) ? p2 : p1;
                    for (NetworkListener l : listeners) l.onGameStarted(opponent);
                }
                break;

            case Protocol.MOVE:
                handleMoveCommand(packet);
                break;

            case Protocol.GAMEOVER:
                String reason = packet.getArg(0);
                String winner = (packet.getArgCount() > 1) ? packet.getArg(1) : "No one";
                for (NetworkListener l : listeners) l.onGameOver(reason, winner);
                break;

            case Protocol.LIST:
            case Protocol.LOBBY_STATS:
                int splitIndex = message.indexOf(Protocol.DELIMITER);
                String info = (splitIndex != -1) ? message.substring(splitIndex + 1) : "";
                for (NetworkListener l : listeners) l.onListReceived(info);
                break;

            case Protocol.ERROR:
                String errorMsg = (packet.getArgCount() > 0) ? packet.getArg(0) : "Unknown Error";
                for (NetworkListener l : listeners) l.onError("Server Error: " + errorMsg);
                break;
        }
    }

    private void handleMoveCommand(Packet packet) {
        int index = -1;
        int pieceId;

        try {
            if (packet.getArgCount() == 1) {
                pieceId = Integer.parseInt(packet.getArg(0));
            } else {
                index = Integer.parseInt(packet.getArg(0));
                pieceId = Integer.parseInt(packet.getArg(1));
            }

            for (NetworkListener l : listeners) l.onMoveReceived(index, pieceId);

        } catch (NumberFormatException e) {
        }
    }

    @Override
    protected void handleDisconnect() {
        for (NetworkListener l : listeners) l.onError("Connection lost!");
    }

    @Override
    protected void handleStart() {

    }
}