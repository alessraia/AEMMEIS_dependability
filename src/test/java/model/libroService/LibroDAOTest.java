package model.libroService;

import model.ConPool;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

public class LibroDAOTest {

    @Test
    public void testDoRetrieveById_found() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true);
        when(rs.getString(1)).thenReturn("ISBN1");
        when(rs.getString(2)).thenReturn("Titolo");
        when(rs.getString(3)).thenReturn("Genere");
        when(rs.getString(4)).thenReturn("2020");
        when(rs.getDouble(5)).thenReturn(12.5);
        when(rs.getInt(6)).thenReturn(10);
        when(rs.getString(7)).thenReturn("Trama");
        when(rs.getString(8)).thenReturn("img.png");
        when(rs.getBoolean(9)).thenReturn(true);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO spyDao = spy(new LibroDAO());
            Autore a = new Autore();
            a.setCf("CF1");
            List<Autore> authors = new ArrayList<>();
            authors.add(a);
            doReturn(authors).when(spyDao).getScrittura("ISBN1");

            Libro result = spyDao.doRetrieveById("ISBN1");

            assertNotNull(result);
            assertEquals("ISBN1", result.getIsbn());
            assertEquals("Titolo", result.getTitolo());
            assertEquals(12.5, result.getPrezzo());
            assertEquals(1, result.getAutori().size());
        }
    }

    @Test
    public void testSearch_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, true, false);
        when(rs.getString(1)).thenReturn("ISBN1", "ISBN2");
        when(rs.getString(2)).thenReturn("T1", "T2");
        when(rs.getString(3)).thenReturn("G1", "G2");
        when(rs.getString(4)).thenReturn("2020", "2021");
        when(rs.getDouble(5)).thenReturn(10.0, 20.0);
        when(rs.getInt(6)).thenReturn(0, 5);
        when(rs.getString(7)).thenReturn("tr1", "tr2");
        when(rs.getString(8)).thenReturn("i1.png", "i2.png");
        when(rs.getBoolean(9)).thenReturn(true, false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO spyDao = spy(new LibroDAO());
            doReturn(Collections.emptyList()).when(spyDao).getScrittura(anyString());

            List<Libro> list = spyDao.Search("query");

            assertNotNull(list);
            assertEquals(2, list.size());
            assertEquals("ISBN1", list.get(0).getIsbn());
            assertEquals("ISBN2", list.get(1).getIsbn());
        }
    }

    @Test
    public void testAddAutore_insertsAndSavesNewAutore() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Autore newAut = new Autore();
            newAut.setCf("CFA");

            try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                    (mock, ctx) -> {
                        when(mock.searchAutore("CFA")).thenReturn(null);
                    })) {

                LibroDAO dao = new LibroDAO();
                dao.addAutore("ISBNX", newAut);

                // verify Scrittura insert executed
                verify(ps).setString(1, "CFA");
                verify(ps).setString(2, "ISBNX");
                verify(ps).executeUpdate();

                AutoreDAO constructed = mocked.constructed().get(0);
                verify(constructed).doSave(newAut);
            }
        }
    }

}
