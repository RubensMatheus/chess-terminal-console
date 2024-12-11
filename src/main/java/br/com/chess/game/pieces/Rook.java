package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessPiece;
import br.com.chess.game.chess.exceptions.ChessException;
import br.com.chess.game.chess.utils.Color;

/*@ skipesc */
public class Rook extends ChessPiece {

    //@ public represents maxMove = 8;

    public Rook(Board board, Color color) {
        super(board, color);
    }

    /*@ public normal_behavior
      @     ensures \result.equals("T");
      @ pure
      @*/
    public String getString(){
        return "T";
    }


    //  to fazendooooo
    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getColumns()];
        Position p = new Position(0, 0);

        // above
        p.setValues(position.getRow() - 1, position.getColumn());

        /*@ maintaining getBoard().positionExists(p) ==>
          @     (p.getRow() >= 0 && p.getRow() < getBoard().getRows());
          @ maintaining (\forall int r; p.getRow() <= r && r < position.getRow();
          @     mat[r][position.getColumn()] == (getBoard().pieces[r][position.getColumn()] == null));
          @ decreasing p.getRow();
          @*/
        while (getBoard().positionExists(p)) {
            mat[p.getRow()][p.getColumn()] = !getBoard().thereIsAPiece(p);
            p.setRow(p.getRow() - 1);
        }

        /*@ refining ensures getBoard().positionExists(p) && isThereOpponentPiece(p) ==>
          @     mat[p.getRow()][p.getColumn()] == true;
          @*/
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        // left
        p.setValues(position.getRow(), position.getColumn() - 1);
        while (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
            p.setColumn(p.getColumn() - 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        // right
        p.setValues(position.getRow(), position.getColumn() + 1);
        while (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
            p.setColumn(p.getColumn() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        // below
        p.setValues(position.getRow() + 1, position.getColumn());
        while (getBoard().positionExists(p) && !getBoard().thereIsAPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
            p.setRow(p.getRow() + 1);
        }
        if (getBoard().positionExists(p) && isThereOpponentPiece(p)) {
            mat[p.getRow()][p.getColumn()] = true;
        }

        return mat;
    }


}

