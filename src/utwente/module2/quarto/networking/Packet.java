package utwente.module2.quarto.networking;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Packet {
    private final String command;
    private final List<String> args;

    public Packet(String input) {
        if (input == null || input.isEmpty()) {
            this.command = "";
            this.args = new ArrayList<>();
            return;
        }

        String[] split = input.split(Protocol.DELIMITER, -1);
        this.command = split[0];

        this.args = new ArrayList<>();
        if (split.length > 1) {
            this.args.addAll(Arrays.asList(split).subList(1, split.length));
        }
    }

    public String getCommand() {
        return command;
    }

    public int getArgCount() {
        return args.size();
    }

    public String getArg(int index) {
        if (index >= 0 && index < args.size()) {
            return args.get(index);
        }
        return null;
    }

    @Override
    public String toString() {
        return "Packet{cmd='" + command + "', args=" + args + "}";
    }
}