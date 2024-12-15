package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.ChessPiece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.utils.Color;

public class Bishop extends ChessPiece {
    //@ public represents maxMove = 7;

    /*@ public normal_behavior
      @     ensures modelColor == color;
      @     ensures modelBoard == board;
      @ pure
      @*/
    public Bishop(Board board, Color color) {
        super(board, color);
    }

    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getColumns()];

        if(position == null || !getBoard().positionExists(position)) {
            return mat;
        }

        //@ assert position.getColumn() + maxMove <= Integer.MAX_VALUE;
        //@ assert position.getRow() + maxMove <= Integer.MAX_VALUE;

        Position p = new Position(0,0);

        int[][] directions = {
                {-1, -1}, // northwest
                {-1,  1}, // northeast
                { 1,  1}, // southeast
                { 1, -1}  // southwest
        };

        /*@ maintaining 0 <= i && i <= directions.length;
          @ maintaining (\forall int x, y;
          @     0 <= x && x < mat.length && 0 <= y && y < mat[x].length;
          @     mat[x][y] ==> (
          @         getBoard().positionExistsBasic(x, y) &&
          @         (getBoard().pieces[x][y] == null ||
          @         (getBoard().pieces[x][y] instanceof ChessPiece &&
          @          getBoard().pieces[x][y].getColor() != this.getColor()))));
          @ decreasing directions.length - i;
          @*/
        for (int i = 0; i < directions.length; i++) {
            int dx = directions[i][0];
            int dy = directions[i][1];

            p.setValues(position.getRow(), position.getColumn());

            /*@ maintaining getBoard().positionExistsBasic(p.getRow(), p.getColumn());
              @ maintaining 0 <= p.getRow() && p.getRow() < getBoard().getRows();
              @ maintaining 0 <= p.getColumn() && p.getColumn() < getBoard().getColumns();
              @ maintaining (\forall int x, y;
              @     0 <= x && x < mat.length && 0 <= y && y < mat[x].length;
              @     mat[x][y] ==> (
              @         getBoard().positionExistsBasic(x, y) &&
              @         (getBoard().pieces[x][y] == null ||
              @         (getBoard().pieces[x][y] instanceof ChessPiece &&
              @          getBoard().pieces[x][y].getColor() != this.getColor()))));
              @ decreasing dx == 1 ? (getBoard().getRows() - p.getRow()) : (p.getRow());
              @*/
            while (getBoard().positionExists(new Position(p.getRow() + dx, p.getColumn() + dy))) {
                p.setValues(p.getRow() + dx, p.getColumn() + dy);

                if (!getBoard().thereIsAPiece(p)) {
                    mat[p.getRow()][p.getColumn()] = true;
                } else {
                    mat[p.getRow()][p.getColumn()] = isThereOpponentPiece(p);
                    break;
                }
            }
        }

        //@ assert (\forall int i, j;
        //@         0 <= i && i < mat.length &&
        //@         0 <= j && j < mat[i].length;
        //@         mat[i][j] ==> (
        //@             getBoard().positionExistsBasic(i, j) &&
        //@             (getBoard().pieces[i][j] == null ||
        //@             (getBoard().pieces[i][j] instanceof ChessPiece &&
        //@               (getBoard().pieces[i][j]).getColor() != this.getColor()))));

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @     ensures \result.equals("B");
      @ pure
      @*/
    @Override
    public String getString(){
        return "B";
    }
}

