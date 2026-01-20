//package ss.tictactoe.ai;
//
//import ss.tictactoe.Game;
//import ss.tictactoe.Move;
//import ss.tictactoe.ui.AbstractPlayer;
//
///**
// * Represents a computer-controlled player.
// * The move is determined by a strategy.
// */
//public class ComputerPlayer extends AbstractPlayer {
//
//    /**
//     * The mark (XX or OO) of this player.
//     */
//    private Mark mark;
//
//    /**
//     * The strategy used to determine moves.
//     */
//    private Strategy strategy;
//
//    /**
//     * Creates a computer player with the given mark and strategy.
//     *
//     * @param mark     the mark of the player
//     * @param strategy the strategy to determine moves
//     */
//    /*@
//      @ requires mark != null;
//      @ requires strategy != null;
//      @ ensures getStrategy() == strategy;
//      @*/
//    public ComputerPlayer(Mark mark, Strategy strategy) {
//        // Name is composed of strategy name + mark
//        super(strategy.getName() + "-" + mark.toString());
//        this.mark = mark;
//        this.strategy = strategy;
//    }
//
//    /**
//     * Determines the next move using the assigned strategy.
//     *
//     * @param game the current game
//     * @return the move chosen by the strategy
//     */
//    /*@
//      @ requires game != null;
//      @ ensures \result != null;
//      @*/
//    @Override
//    public Move determineMove(Game game) {
//        return strategy.determineMove(game);
//    }
//
//    /**
//     * Returns the current strategy.
//     *
//     * @return the strategy
//     */
//    /*@
//      @ ensures \result == strategy;
//      @*/
//    public Strategy getStrategy() {
//        return strategy;
//    }
//
//    /**
//     * Sets a new strategy for the player.
//     *
//     * @param strategy the new strategy
//     */
//    /*@
//      @ requires strategy != null;
//      @ ensures getStrategy() == strategy;
//      @*/
//    public void setStrategy(Strategy strategy) {
//        this.strategy = strategy;
//    }
//}
