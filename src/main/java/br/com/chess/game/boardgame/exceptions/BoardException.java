package br.com.chess.game.boardgame.exceptions;

public class BoardException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    //@ pure
    public BoardException(String msg){
        super(msg);
    }
}
