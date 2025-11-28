package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test class for AggiungiRepartoServlet
 * Tests the functionality of adding a new department (Reparto) to the system
 */
class AggiungiRepartoServletTest {

    private AggiungiRepartoServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;
    private RepartoDAO repartoDAO;

    @BeforeEach
    void setUp() {
        servlet = new AggiungiRepartoServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        repartoDAO = mock(RepartoDAO.class);
    }

    /**
     * Test successful addition of a new reparto with valid parameters
     * Expected: redirect to "gestisci-reparti"
     */
    @Test
    void testDoGet_SuccessfulAddition() throws Exception {
        when(request.getParameter("nome")).thenReturn("Narrativa");
        when(request.getParameter("descrizione")).thenReturn("Libri di narrativa italiana e straniera");
        when(request.getParameter("immagine")).thenReturn("narrativa.jpg");

        when(repartoDAO.doRetrivedAll()).thenReturn(Collections.emptyList());
        doNothing().when(repartoDAO).doSave(any(Reparto.class));

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).doSave(any(Reparto.class));
        verify(response).sendRedirect("gestisci-reparti");
        verify(dispatcher, never()).forward(request, response);
    }

    /**
     * Test when nome parameter is null
     * Expected: redirect to error page
     */
    @Test
    void testDoGet_NomeNull() throws Exception {
        when(request.getParameter("nome")).thenReturn(null);
        when(request.getParameter("descrizione")).thenReturn("Descrizione valida");
        when(request.getParameter("immagine")).thenReturn("image.jpg");

        servlet.doGet(request, response);

        verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(repartoDAO, never()).doRetrivedAll();
        verify(repartoDAO, never()).doSave(any(Reparto.class));
    }

    /**
     * Test when nome parameter is empty string
     * Expected: redirect to error page
     */
    @Test
    void testDoGet_NomeEmpty() throws Exception {
        when(request.getParameter("nome")).thenReturn("");
        when(request.getParameter("descrizione")).thenReturn("Descrizione valida");
        when(request.getParameter("immagine")).thenReturn("image.jpg");

        servlet.doGet(request, response);

        verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(repartoDAO, never()).doRetrivedAll();
        verify(repartoDAO, never()).doSave(any(Reparto.class));
    }

    /**
     * Test when descrizione parameter is null
     * Expected: redirect to error page
     */
    @Test
    void testDoGet_DescrizioneNull() throws Exception {
        when(request.getParameter("nome")).thenReturn("Narrativa");
        when(request.getParameter("descrizione")).thenReturn(null);
        when(request.getParameter("immagine")).thenReturn("image.jpg");

        servlet.doGet(request, response);

        verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(repartoDAO, never()).doRetrivedAll();
        verify(repartoDAO, never()).doSave(any(Reparto.class));
    }

    /**
     * Test when descrizione parameter is empty string
     * Expected: redirect to error page
     */
    @Test
    void testDoGet_DescrizioneEmpty() throws Exception {
        when(request.getParameter("nome")).thenReturn("Narrativa");
        when(request.getParameter("descrizione")).thenReturn("");
        when(request.getParameter("immagine")).thenReturn("image.jpg");

        servlet.doGet(request, response);

        verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(repartoDAO, never()).doRetrivedAll();
        verify(repartoDAO, never()).doSave(any(Reparto.class));
    }

    /**
     * Test when immagine parameter is null
     * Expected: redirect to error page
     */
    @Test
    void testDoGet_ImmagineNull() throws Exception {
        when(request.getParameter("nome")).thenReturn("Narrativa");
        when(request.getParameter("descrizione")).thenReturn("Descrizione valida");
        when(request.getParameter("immagine")).thenReturn(null);

        servlet.doGet(request, response);

        verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(repartoDAO, never()).doRetrivedAll();
        verify(repartoDAO, never()).doSave(any(Reparto.class));
    }

    /**
     * Test when immagine parameter is empty string
     * Expected: redirect to error page
     */
    @Test
    void testDoGet_ImmagineEmpty() throws Exception {
        when(request.getParameter("nome")).thenReturn("Narrativa");
        when(request.getParameter("descrizione")).thenReturn("Descrizione valida");
        when(request.getParameter("immagine")).thenReturn("");

        servlet.doGet(request, response);

        verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(repartoDAO, never()).doRetrivedAll();
        verify(repartoDAO, never()).doSave(any(Reparto.class));
    }

    /**
     * Test when reparto with same name already exists (covers duplicate check branch)
     * Expected: forward to aggiungiReparto.jsp with error message
     */
    @Test
    void testDoGet_RepartoAlreadyExists() throws Exception {
        when(request.getParameter("nome")).thenReturn("Narrativa");
        when(request.getParameter("descrizione")).thenReturn("Descrizione nuova");
        when(request.getParameter("immagine")).thenReturn("nuova.jpg");

        Reparto existingReparto = new Reparto();
        existingReparto.setNome("Narrativa");
        existingReparto.setDescrizione("Descrizione vecchia");
        existingReparto.setImmagine("vecchia.jpg");

        List<Reparto> existingReparti = new ArrayList<>();
        existingReparti.add(existingReparto);

        when(repartoDAO.doRetrivedAll()).thenReturn(existingReparti);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/aggiungiReparto.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(request).setAttribute("esito", "non riuscito");
        verify(dispatcher).forward(request, response);
        verify(repartoDAO, never()).doSave(any(Reparto.class));
        verify(response, never()).sendRedirect(anyString());
    }

    /**
     * Test when reparto with different name exists
     * Expected: redirect to "gestisci-reparti"
     */
    @Test
    void testDoGet_DifferentRepartoExists() throws Exception {
        when(request.getParameter("nome")).thenReturn("Narrativa");
        when(request.getParameter("descrizione")).thenReturn("Libri di narrativa");
        when(request.getParameter("immagine")).thenReturn("narrativa.jpg");

        Reparto existingReparto = new Reparto();
        existingReparto.setNome("Saggistica");
        existingReparto.setDescrizione("Libri di saggistica");
        existingReparto.setImmagine("saggistica.jpg");

        List<Reparto> existingReparti = new ArrayList<>();
        existingReparti.add(existingReparto);

        when(repartoDAO.doRetrivedAll()).thenReturn(existingReparti);
        doNothing().when(repartoDAO).doSave(any(Reparto.class));

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).doSave(any(Reparto.class));
        verify(response).sendRedirect("gestisci-reparti");
        verify(dispatcher, never()).forward(request, response);
    }

    /**
     * Test with whitespace-only parameters (covers trim + isEmpty validation)
     * Expected: redirect to error page
     */
    @Test
    void testDoGet_WhitespaceOnlyParameters() throws Exception {
        when(request.getParameter("nome")).thenReturn("   ");
        when(request.getParameter("descrizione")).thenReturn("   ");
        when(request.getParameter("immagine")).thenReturn("   ");

        servlet.doGet(request, response);

        verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(repartoDAO, never()).doRetrivedAll();
        verify(repartoDAO, never()).doSave(any(Reparto.class));
    }

    /**
     * Test that setDescrizione() is called with correct value on successful addition
     * Expected: saved Reparto object has correct descrizione
     */
    @Test
    void testDoGet_VerifyDescrizioneIsSet() throws Exception {
        when(request.getParameter("nome")).thenReturn("Fantascienza");
        when(request.getParameter("descrizione")).thenReturn("Libri di fantascienza e distopia");
        when(request.getParameter("immagine")).thenReturn("fantascienza.jpg");

        when(repartoDAO.doRetrivedAll()).thenReturn(Collections.emptyList());
        doNothing().when(repartoDAO).doSave(any(Reparto.class));

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        // Capture the Reparto object passed to doSave
        ArgumentCaptor<Reparto> captor = ArgumentCaptor.forClass(Reparto.class);
        verify(repartoDAO).doSave(captor.capture());

        Reparto savedReparto = captor.getValue();
        assertEquals("Libri di fantascienza e distopia", savedReparto.getDescrizione(),
                "setDescrizione() should set the description correctly");
    }

    /**
     * Test that setImmagine() is called with correct value on successful addition
     * Expected: saved Reparto object has correct immagine
     */
    @Test
    void testDoGet_VerifyImmagineIsSet() throws Exception {
        when(request.getParameter("nome")).thenReturn("Gialli");
        when(request.getParameter("descrizione")).thenReturn("Romanzi gialli e thriller");
        when(request.getParameter("immagine")).thenReturn("gialli.jpg");

        when(repartoDAO.doRetrivedAll()).thenReturn(Collections.emptyList());
        doNothing().when(repartoDAO).doSave(any(Reparto.class));

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        // Capture the Reparto object passed to doSave
        ArgumentCaptor<Reparto> captor = ArgumentCaptor.forClass(Reparto.class);
        verify(repartoDAO).doSave(captor.capture());

        Reparto savedReparto = captor.getValue();
        assertEquals("gialli.jpg", savedReparto.getImmagine(),
                "setImmagine() should set the image correctly");
    }

    /**
     * Test that all three setter methods are called with correct values on successful addition
     * Expected: saved Reparto object has all fields set correctly
     */
    @Test
    void testDoGet_VerifyAllSetttersAreCalled() throws Exception {
        when(request.getParameter("nome")).thenReturn("Cucina");
        when(request.getParameter("descrizione")).thenReturn("Libri di ricette e cucina");
        when(request.getParameter("immagine")).thenReturn("cucina.jpg");

        when(repartoDAO.doRetrivedAll()).thenReturn(Collections.emptyList());
        doNothing().when(repartoDAO).doSave(any(Reparto.class));

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        // Capture the Reparto object passed to doSave
        ArgumentCaptor<Reparto> captor = ArgumentCaptor.forClass(Reparto.class);
        verify(repartoDAO).doSave(captor.capture());

        Reparto savedReparto = captor.getValue();
        assertEquals("Cucina", savedReparto.getNome(),
                "setNome() should set the name correctly");
        assertEquals("Libri di ricette e cucina", savedReparto.getDescrizione(),
                "setDescrizione() should set the description correctly");
        assertEquals("cucina.jpg", savedReparto.getImmagine(),
                "setImmagine() should set the image correctly");
    }
}
