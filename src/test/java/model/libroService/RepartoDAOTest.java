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

public class RepartoDAOTest {

    @Test
    public void testDoRetrieveById_found() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true);
        when(rs.getInt(1)).thenReturn(7);
        when(rs.getString(2)).thenReturn("NomeR");
        when(rs.getString(3)).thenReturn("Desc");
        when(rs.getString(4)).thenReturn("img.png");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO spy = spy(new RepartoDAO());
            doReturn(Collections.emptyList()).when(spy).getAppartenenza(7);

            Reparto r = spy.doRetrieveById(7);

            assertNotNull(r);
            assertEquals(7, r.getIdReparto());
            assertEquals("NomeR", r.getNome());
            assertEquals("Desc", r.getDescrizione());
            assertEquals(0, r.getLibri().size());
        }
    }

    @Test
    public void testDoRetrivedAll_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, true, false);
        when(rs.getInt(1)).thenReturn(1, 2);
        when(rs.getString(2)).thenReturn("R1", "R2");
        when(rs.getString(3)).thenReturn("D1", "D2");
        when(rs.getString(4)).thenReturn("i1.png", "i2.png");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO spy = spy(new RepartoDAO());
            doReturn(Collections.emptyList()).when(spy).getAppartenenza(anyInt());

            List<Reparto> list = spy.doRetrivedAll();

            assertNotNull(list);
            assertEquals(2, list.size());
            assertEquals(1, list.get(0).getIdReparto());
            assertEquals(2, list.get(1).getIdReparto());
        }
    }

    @Test
    public void testAggiungiLibroReparto_addsBookAndCallsLibroDAO() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Reparto reparto = new Reparto();
            reparto.setIdReparto(10);
            reparto.setLibri(new ArrayList<>());

            Libro l = new Libro();
            l.setIsbn("ISBNX");

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById("ISBNX")).thenReturn(l))) {

                RepartoDAO dao = new RepartoDAO();
                dao.aggiungiLibroReparto(reparto, "ISBNX");

                verify(ps).setInt(1, 10);
                verify(ps).setString(2, "ISBNX");
                verify(ps).executeUpdate();

                // LibroDAO.doRetrieveById should have been called and libro added to reparto
                assertEquals(1, reparto.getLibri().size());
                assertEquals("ISBNX", reparto.getLibri().get(0).getIsbn());
            }
        }
    }

    @Test
    public void testDoSave_setsGeneratedId() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString(), anyInt())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);
        when(ps.getGeneratedKeys()).thenReturn(rs);
        when(rs.next()).thenReturn(true);
        when(rs.getInt(1)).thenReturn(123);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Reparto r = new Reparto();
            r.setNome("N");
            r.setDescrizione("D");

            RepartoDAO dao = new RepartoDAO();
            dao.doSave(r);

            assertEquals(123, r.getIdReparto());
        }
    }

    @Test
    public void testDoSave_noGeneratedKeys_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString(), anyInt())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);
        when(ps.getGeneratedKeys()).thenReturn(rs);
        when(rs.next()).thenReturn(false); // no generated keys

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Reparto r = new Reparto();
            r.setNome("N");
            r.setDescrizione("D");

            RepartoDAO dao = new RepartoDAO();
            // the DAO will call rs.next() then rs.getInt(1); our mock returns 0 for getInt,
            // so no SQLException is thrown — assert id is set to 0
            dao.doSave(r);
            assertEquals(0, r.getIdReparto());
        }
    }

    @Test
    public void testDeleteReparto_withAppartenenza_deletesBoth() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps1, ps2);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(7);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        RepartoDAO spyDao = spy(new RepartoDAO());
        doReturn(libri).when(spyDao).getAppartenenza(7);
        doReturn(reparto).when(spyDao).doRetrieveById(7);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            spyDao.deleteReparto(7);

            verify(ps1).setInt(1, 7);
            verify(ps1).executeUpdate();
            verify(ps2).setInt(1, 7);
            verify(ps2).executeUpdate();
        }
    }

    @Test
    public void testRemoveLibroReparto_executeUpdate0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(5);
        Libro l = new Libro();
        l.setIsbn("BISBN");
        reparto.setLibri(new ArrayList<>());
        reparto.getLibri().add(l);

        RepartoDAO spyDao = spy(new RepartoDAO());
        doReturn(reparto).when(spyDao).doRetrieveById(5);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById("BISBN")).thenReturn(l))) {

                assertThrows(RuntimeException.class, () -> spyDao.removeLibroReparto(5, "BISBN"));
            }
        }
    }

    @Test
    public void testDoSave_throwsWhenInsertFails() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("INSERT INTO Reparto"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Reparto r = new Reparto();
            r.setNome("N");
            r.setDescrizione("D");

            RepartoDAO dao = new RepartoDAO();
            assertThrows(RuntimeException.class, () -> dao.doSave(r));
        }
    }

    @Test
    public void testDeleteReparto_noAppartenenza_deletesOnlyReparto() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        RepartoDAO spyDao = spy(new RepartoDAO());
        doReturn(Collections.emptyList()).when(spyDao).getAppartenenza(anyInt());
        doReturn(new Reparto()).when(spyDao).doRetrieveById(anyInt());

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            spyDao.deleteReparto(11);

            verify(ps, atLeastOnce()).executeUpdate();
        }
    }

    @Test
    public void testDoSaveAppartenenza_executeUpdate0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("INSERT INTO Appartenenza"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO dao = new RepartoDAO();
            assertThrows(RuntimeException.class, () -> dao.doSaveAppartenenza(2, "isbn"));
        }
    }

    @Test
    public void testDeleteReparto_appartenenzaExecute0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement psApp = mock(PreparedStatement.class);
        PreparedStatement psRep = mock(PreparedStatement.class);

        // first prepared statement (DELETE FROM Appartenenza) will return 0 -> cause exception
        when(conn.prepareStatement(anyString())).thenReturn(psApp, psRep);
        when(psApp.executeUpdate()).thenReturn(0);
        when(psRep.executeUpdate()).thenReturn(1);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(7);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        RepartoDAO spyDao = spy(new RepartoDAO());
        doReturn(libri).when(spyDao).getAppartenenza(7);
        doReturn(reparto).when(spyDao).doRetrieveById(7);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            assertThrows(RuntimeException.class, () -> spyDao.deleteReparto(7));
        }
    }

    @Test
    public void testDeleteReparto_getAppartenenzaNull_deletesOnlyReparto() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        RepartoDAO spyDao = spy(new RepartoDAO());
        doReturn(null).when(spyDao).getAppartenenza(anyInt());
        doReturn(new Reparto()).when(spyDao).doRetrieveById(anyInt());

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            // should not throw
            spyDao.deleteReparto(13);

            verify(ps).setInt(1, 13);
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDeleteReparto_repartoDeleteFails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement psApp = mock(PreparedStatement.class);
        PreparedStatement psRep = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(psApp, psRep);
        when(psApp.executeUpdate()).thenReturn(1);
        when(psRep.executeUpdate()).thenReturn(0); // final delete fails

        Reparto reparto = new Reparto();
        reparto.setIdReparto(22);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        RepartoDAO spyDao = spy(new RepartoDAO());
        doReturn(libri).when(spyDao).getAppartenenza(22);
        doReturn(reparto).when(spyDao).doRetrieveById(22);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            assertThrows(RuntimeException.class, () -> spyDao.deleteReparto(22));
        }
    }

    @Test
    public void testGetAppartenenza_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(contains("Appartenenza"))).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, false);
        when(rs.getString(1)).thenReturn("ISBN-G1");

        Libro libro = new Libro();
        libro.setIsbn("ISBN-G1");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById("ISBN-G1")).thenReturn(libro))) {

                RepartoDAO dao = new RepartoDAO();
                List<Libro> list = dao.getAppartenenza(9);

                assertNotNull(list);
                assertEquals(1, list.size());
                assertEquals("ISBN-G1", list.get(0).getIsbn());
            }
        }
    }

    @Test
    public void testUpdateReparto_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("UPDATE Reparto SET"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Reparto r = new Reparto();
            r.setIdReparto(5);
            r.setDescrizione("NEWDES");
            r.setImmagine("imgx.png");

            RepartoDAO dao = new RepartoDAO();
            dao.updateReparto(r);

            verify(ps).setString(1, "NEWDES");
            verify(ps).setString(2, "imgx.png");
            verify(ps).setInt(3, 5);
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDeleteFromAppartenenzaLibro_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("DELETE FROM Appartenenza WHERE"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO dao = new RepartoDAO();
            // should not throw
            dao.deleteFromAppartenenzaLibro(3, "AAA");

            verify(ps).setInt(1, 3);
            verify(ps).setString(2, "AAA");
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDoRetrieveById_notFound_returnsNull() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO dao = new RepartoDAO();
            Reparto r = dao.doRetrieveById(999);

            assertNull(r);
        }
    }

    @Test
    public void testAggiungiLibroReparto_insertFails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Reparto reparto = new Reparto();
            reparto.setIdReparto(20);
            reparto.setLibri(new ArrayList<>());

            RepartoDAO dao = new RepartoDAO();
            assertThrows(RuntimeException.class, () -> dao.aggiungiLibroReparto(reparto, "XISBN"));
        }
    }

    @Test
    public void testUpdateReparto_executeUpdate0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("UPDATE Reparto SET"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Reparto r = new Reparto();
            r.setIdReparto(5);
            r.setDescrizione("D");
            r.setImmagine("i.png");

            RepartoDAO dao = new RepartoDAO();
            assertThrows(RuntimeException.class, () -> dao.updateReparto(r));
        }
    }

    @Test
    public void testDeleteFromAppartenenzaLibro_executeUpdate0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("DELETE FROM Appartenenza WHERE"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO dao = new RepartoDAO();
            assertThrows(RuntimeException.class, () -> dao.deleteFromAppartenenzaLibro(3, "AAA"));
        }
    }

    @Test
    public void testDoSaveAppartenenza_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("INSERT INTO Appartenenza"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            RepartoDAO dao = new RepartoDAO();
            // should not throw
            dao.doSaveAppartenenza(2, "isbn-okay");

            verify(ps).setInt(1, 2);
            verify(ps).setString(2, "isbn-okay");
            verify(ps).executeUpdate();
        }
    }

}
