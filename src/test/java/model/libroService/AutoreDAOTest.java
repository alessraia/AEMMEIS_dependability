package model.libroService;

import model.ConPool;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

public class AutoreDAOTest {

    @Test
    public void testDoSave_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString(), anyInt())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            AutoreDAO dao = new AutoreDAO();
            Autore a = new Autore();
            a.setCf("CF123");
            a.setNome("Mario");
            a.setCognome("Rossi");

            dao.doSave(a);

            verify(ps).setString(1, "CF123");
            verify(ps).setString(2, "Mario");
            verify(ps).setString(3, "Rossi");
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDeleteAutore_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            AutoreDAO dao = new AutoreDAO();
            dao.deleteAutore("CFDEL");

            verify(ps).setString(1, "CFDEL");
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testSearchAutore_found() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true);
        when(rs.getString(1)).thenReturn("Luca");
        when(rs.getString(2)).thenReturn("Bianchi");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            AutoreDAO dao = new AutoreDAO();
            Autore a = dao.searchAutore("CFSRCH");

            assertNotNull(a);
            assertEquals("CFSRCH", a.getCf());
            assertEquals("Luca", a.getNome());
            assertEquals("Bianchi", a.getCognome());
        }
    }

    @Test
    public void testGetScrittura_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        // First call -> true (isbn1), second -> true (isbn2), then false
        when(rs.next()).thenReturn(true, true, false);
        when(rs.getString(1)).thenReturn("ISBN1", "ISBN2");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Libro l1 = new Libro();
            l1.setIsbn("ISBN1");
            Libro l2 = new Libro();
            l2.setIsbn("ISBN2");

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, context) -> {
                        when(mock.doRetrieveById("ISBN1")).thenReturn(l1);
                        when(mock.doRetrieveById("ISBN2")).thenReturn(l2);
                    })) {

                AutoreDAO dao = new AutoreDAO();
                List<Libro> list = dao.getScrittura("CFSCR");

                assertNotNull(list);
                assertEquals(2, list.size());
                assertEquals("ISBN1", list.get(0).getIsbn());
                assertEquals("ISBN2", list.get(1).getIsbn());
            }
        }
    }

    @Test
    public void testDoSave_failure_throwsRuntimeException_whenExecuteUpdateNot1() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString(), anyInt())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            AutoreDAO dao = new AutoreDAO();
            Autore a = new Autore();
            a.setCf("CFERR");
            a.setNome("Nome");
            a.setCognome("Cognome");

            assertThrows(RuntimeException.class, () -> dao.doSave(a));
        }
    }

    @Test
    public void testDeleteAutore_failure_throwsRuntimeException_whenExecuteUpdateNot1() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            AutoreDAO dao = new AutoreDAO();
            assertThrows(RuntimeException.class, () -> dao.deleteAutore("CFDELERR"));
        }
    }

    @Test
    public void testSearchAutore_notFound_returnsNull() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            AutoreDAO dao = new AutoreDAO();
            Autore a = dao.searchAutore("CFNOT");

            assertNull(a);
        }
    }

    @Test
    public void testGetScrittura_empty_returnsEmptyList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            AutoreDAO dao = new AutoreDAO();
            List<Libro> list = dao.getScrittura("CFSCR_EMPTY");

            assertNotNull(list);
            assertEquals(0, list.size());
        }
    }

    @Test
    public void testDoSave_sqlException_wrapped() throws Exception {
        Connection conn = mock(Connection.class);

        when(conn.prepareStatement(anyString(), anyInt())).thenThrow(new java.sql.SQLException("fail"));

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            AutoreDAO dao = new AutoreDAO();
            Autore a = new Autore();
            a.setCf("CFSQL");
            a.setNome("N");
            a.setCognome("C");

            assertThrows(RuntimeException.class, () -> dao.doSave(a));
        }
    }

    @Test
    public void testGetScrittura_libroDaoReturnsNull_listContainsNull() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, false);
        when(rs.getString(1)).thenReturn("ISBN_NULL");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, context) -> {
                        when(mock.doRetrieveById("ISBN_NULL")).thenReturn(null);
                    })) {

                AutoreDAO dao = new AutoreDAO();
                List<Libro> list = dao.getScrittura("CFSCR_NULL");

                assertNotNull(list);
                assertEquals(1, list.size());
                assertNull(list.get(0));
            }
        }
    }

}
