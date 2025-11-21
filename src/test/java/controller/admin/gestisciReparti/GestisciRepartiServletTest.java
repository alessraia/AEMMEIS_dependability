package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.mockito.Mockito.*;

/**
 * Test class for GestisciRepartiServlet
 * Tests the functionality of retrieving and displaying all departments (Reparti) in the system
 */
class GestisciRepartiServletTest {

    private GestisciRepartiServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;
    private RepartoDAO repartoDAO;

    @BeforeEach
    void setUp() {
        servlet = new GestisciRepartiServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        repartoDAO = mock(RepartoDAO.class);
    }

    /**
     * Test successful retrieval of all reparti with a populated list
     * Expected: reparti list is set as request attribute and forwards to gestisciReparti.jsp
     */
    @Test
    void testDoGet_SuccessfulRetrievalWithMultipleReparti() throws Exception {
        List<Reparto> reparti = new ArrayList<>();
        
        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Narrativa");
        reparto1.setDescrizione("Libri di narrativa");
        reparto1.setImmagine("narrativa.jpg");
        
        Reparto reparto2 = new Reparto();
        reparto2.setIdReparto(2);
        reparto2.setNome("Saggistica");
        reparto2.setDescrizione("Libri di saggistica");
        reparto2.setImmagine("saggistica.jpg");
        
        Reparto reparto3 = new Reparto();
        reparto3.setIdReparto(3);
        reparto3.setNome("Fumetti");
        reparto3.setDescrizione("Fumetti e graphic novel");
        reparto3.setImmagine("fumetti.jpg");
        
        reparti.add(reparto1);
        reparti.add(reparto2);
        reparti.add(reparto3);

        when(repartoDAO.doRetrivedAll()).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).doRetrivedAll();
        verify(request).setAttribute("reparti", reparti);
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test retrieval when database is empty
     * Expected: empty list is set as request attribute and forwards to gestisciReparti.jsp
     */
    @Test
    void testDoGet_EmptyRepartiList() throws Exception {
        List<Reparto> emptyList = Collections.emptyList();

        when(repartoDAO.doRetrivedAll()).thenReturn(emptyList);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).doRetrivedAll();
        verify(request).setAttribute("reparti", emptyList);
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test retrieval with a single reparto
     * Expected: list with one element is set as request attribute and forwards
     */
    @Test
    void testDoGet_SingleReparto() throws Exception {
        List<Reparto> reparti = new ArrayList<>();
        
        Reparto reparto = new Reparto();
        reparto.setIdReparto(1);
        reparto.setNome("Narrativa");
        reparto.setDescrizione("Libri di narrativa italiana e straniera");
        reparto.setImmagine("narrativa.jpg");
        
        reparti.add(reparto);

        when(repartoDAO.doRetrivedAll()).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).doRetrivedAll();
        verify(request).setAttribute("reparti", reparti);
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when doRetrivedAll returns null
     * Expected: null is set as request attribute and forwards
     */
    @Test
    void testDoGet_NullRepartiList() throws Exception {
        when(repartoDAO.doRetrivedAll()).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).doRetrivedAll();
        verify(request).setAttribute("reparti", null);
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when doRetrivedAll throws an exception
     * Expected: exception propagates up
     */
    @Test
    void testDoGet_DoRetrivedAllThrowsException() throws Exception {
        when(repartoDAO.doRetrivedAll()).thenThrow(new RuntimeException("Database connection error"));

        servlet.setRepartoDAO(repartoDAO);

        try {
            servlet.doGet(request, response);
        } catch (RuntimeException e) {
            // Expected exception
        }

        verify(repartoDAO).doRetrivedAll();
        verify(request, never()).setAttribute(anyString(), any());
        verify(dispatcher, never()).forward(request, response);
    }

    /**
     * Test with reparti containing special characters in names
     * Expected: list with special characters is set correctly and forwards
     */
    @Test
    void testDoGet_RepartiWithSpecialCharacters() throws Exception {
        List<Reparto> reparti = new ArrayList<>();
        
        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Narrativa & Poesia");
        reparto1.setDescrizione("Libri di narrativa e poesia <italiana>");
        reparto1.setImmagine("narrativa&poesia.jpg");
        
        Reparto reparto2 = new Reparto();
        reparto2.setIdReparto(2);
        reparto2.setNome("Sci-Fi / Fantasy");
        reparto2.setDescrizione("Libri di fantascienza e fantasy");
        reparto2.setImmagine("scifi_fantasy.jpg");
        
        reparti.add(reparto1);
        reparti.add(reparto2);

        when(repartoDAO.doRetrivedAll()).thenReturn(reparti);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.doGet(request, response);

        verify(repartoDAO).doRetrivedAll();
        verify(request).setAttribute("reparti", reparti);
        verify(dispatcher).forward(request, response);
    }
}
