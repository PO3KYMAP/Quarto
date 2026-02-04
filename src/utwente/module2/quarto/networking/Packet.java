package utwente.module2.quarto.networking;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Represents a network packet parsed from a raw protocol string.
 * Splits the input into a command and a list of arguments based on the protocol delimiter.
 */
public class Packet {

    /*@ private invariant command != null;
        private invariant args != null;
    @*/

    private final String command;
    private final List<String> args;

    /**
     * Constructs a Packet by parsing a raw input string.
     * Splitting is done using the Protocol.DELIMITER.
     *
     * @param input the raw message string to parse.
     */
    /*@ requires true;
        ensures (input == null || input.isEmpty()) ==> (command.equals("") && args.isEmpty());
        ensures (input != null && !input.isEmpty()) ==> command.equals(input.split(Protocol.DELIMITER, -1)[0]);
    @*/
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

    /**
     * Gets the command part of the packet.
     *
     * @return the command string.
     */
    /*@ pure @*/
    public String getCommand() {
        return command;
    }

    /**
     * Gets the number of arguments in the packet.
     *
     * @return the argument count.
     */
    /*@
        ensures \result == args.size();
        pure
    @*/
    public int getArgCount() {
        return args.size();
    }

    /**
     * Retrieves an argument by its index.
     *
     * @param index the index of the argument (0-based).
     * @return the argument string, or null if the index is out of bounds.
     */
    /*@
        ensures (index >= 0 && index < args.size()) ==> \result == args.get(index);
        ensures (index < 0 || index >= args.size()) ==> \result == null;
        pure
    @*/
    public String getArg(int index) {
        if (index >= 0 && index < args.size()) {
            return args.get(index);
        }
        return null;
    }

    /**
     * Returns a string representation of the packet for debugging.
     *
     * @return the string representation.
     */
    @Override
    public String toString() {
        return "Packet{cmd='" + command + "', args=" + args + "}";
    }
}