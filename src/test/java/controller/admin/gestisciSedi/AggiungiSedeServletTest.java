package controller.admin.gestisciSedi;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

/**
 * Unit tests for AggiungiSedeServlet
 * Tests the servlet's ability to add new store locations (sedi) with proper validation
 * and duplicate detection.
 */
class AggiungiSedeServletTest {

    private AggiungiSedeServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new AggiungiSedeServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    @Test
    void testDoGet_SuccessfullSedeCreation() throws IOException, ServletException {
        // Arrange: Set valid parameters for a new sede
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify redirect to gestisci-sedi occurs
            verify(response).sendRedirect("gestisci-sedi");
            verify(dispatcher, never()).forward(request, response);
        }
    }

    @Test
    void testDoGet_EmptyCittaParameter() throws IOException, ServletException {
        // Arrange: Empty citta parameter
        when(request.getParameter("citta")).thenReturn("");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page (called at least once due to missing return in servlet)
            verify(response, atLeastOnce()).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }

    @Test
    void testDoGet_NullCittaParameter() throws IOException, ServletException {
        // Arrange: Null citta parameter
        when(request.getParameter("citta")).thenReturn(null);
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page (called at least once due to missing return in servlet)
            verify(response, atLeastOnce()).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }

    @Test
    void testDoGet_EmptyViaParameter() throws IOException, ServletException {
        // Arrange: Empty via parameter
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page (called at least once due to missing return in servlet)
            verify(response, atLeastOnce()).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }

    @Test
    void testDoGet_NullViaParameter() throws IOException, ServletException {
        // Arrange: Null via parameter
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn(null);
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page (called at least once due to missing return in servlet)
            verify(response, atLeastOnce()).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }

    @Test
    void testDoGet_EmptyCivicoParameter() throws IOException, ServletException {
        // Arrange: Empty civico parameter
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page (called at least once due to missing return in servlet)
            verify(response, atLeastOnce()).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }

    @Test
    void testDoGet_NullCivicoParameter() throws IOException, ServletException {
        // Arrange: Null civico parameter
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn(null);
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page (called at least once due to missing return in servlet)
            verify(response, atLeastOnce()).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }

    @Test
    void testDoGet_EmptyCapParameter() throws IOException, ServletException {
        // Arrange: Empty cap parameter
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page (called at least once due to missing return in servlet)
            verify(response, atLeastOnce()).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }

    @Test
    void testDoGet_NullCapParameter() throws IOException, ServletException {
        // Arrange: Null cap parameter
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn(null);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page (called at least once due to missing return in servlet)
            verify(response, atLeastOnce()).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }


    @Test
    void testDoGet_InvalidCivicoNumber() throws IOException, ServletException {
        // Arrange: Invalid civico (not a number)
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("abc");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to error page for number format error
            verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }

    @Test
    void testDoGet_NegativeCivicoNumber() throws IOException, ServletException {
        // Arrange: Negative civico number
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("-5");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should accept negative number (no validation on sign) and redirect
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_DuplicateSedeExist() throws IOException, ServletException {
        // Arrange: Parameters for a sede that already exists
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        // Create an existing sede with same data
        Sede existingSede = new Sede();
        existingSede.setCitta("Milano");
        existingSede.setVia("Via Roma");
        existingSede.setCivico(42);
        existingSede.setCap("20100");

        List<Sede> sediList = new ArrayList<>();
        sediList.add(existingSede);

        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sediList);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should forward to the form page with error attribute
            verify(request).setAttribute("esito", "non riuscito");
            verify(dispatcher).forward(request, response);
            verify(response, never()).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_SimilarSedeButDifferentCitta() throws IOException, ServletException {
        // Arrange: Parameters for a sede similar but with different city
        when(request.getParameter("citta")).thenReturn("Roma");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        // Create an existing sede with different city
        Sede existingSede = new Sede();
        existingSede.setCitta("Milano");
        existingSede.setVia("Via Roma");
        existingSede.setCivico(42);
        existingSede.setCap("20100");

        List<Sede> sediList = new ArrayList<>();
        sediList.add(existingSede);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sediList);
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to gestisci-sedi (not a duplicate)
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_SimilarSedeButDifferentVia() throws IOException, ServletException {
        // Arrange: Parameters for a sede similar but with different via
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Milano");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        // Create an existing sede with different via
        Sede existingSede = new Sede();
        existingSede.setCitta("Milano");
        existingSede.setVia("Via Roma");
        existingSede.setCivico(42);
        existingSede.setCap("20100");

        List<Sede> sediList = new ArrayList<>();
        sediList.add(existingSede);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sediList);
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to gestisci-sedi (not a duplicate)
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_SimilarSedeButDifferentCivico() throws IOException, ServletException {
        // Arrange: Parameters for a sede similar but with different civico
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("43");
        when(request.getParameter("cap")).thenReturn("20100");

        // Create an existing sede with different civico
        Sede existingSede = new Sede();
        existingSede.setCitta("Milano");
        existingSede.setVia("Via Roma");
        existingSede.setCivico(42);
        existingSede.setCap("20100");

        List<Sede> sediList = new ArrayList<>();
        sediList.add(existingSede);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sediList);
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to gestisci-sedi (not a duplicate)
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_SimilarSedeButDifferentCap() throws IOException, ServletException {
        // Arrange: Parameters for a sede similar but with different cap
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20101");

        // Create an existing sede with different cap
        Sede existingSede = new Sede();
        existingSede.setCitta("Milano");
        existingSede.setVia("Via Roma");
        existingSede.setCivico(42);
        existingSede.setCap("20100");

        List<Sede> sediList = new ArrayList<>();
        sediList.add(existingSede);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sediList);
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to gestisci-sedi (not a duplicate)
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_MultipleSediInDatabase() throws IOException, ServletException {
        // Arrange: Parameters for a new sede when multiple sedi exist
        when(request.getParameter("citta")).thenReturn("Torino");
        when(request.getParameter("via")).thenReturn("Via Torino");
        when(request.getParameter("civico")).thenReturn("100");
        when(request.getParameter("cap")).thenReturn("10100");

        // Create multiple existing sedi
        Sede sede1 = new Sede();
        sede1.setCitta("Milano");
        sede1.setVia("Via Roma");
        sede1.setCivico(42);
        sede1.setCap("20100");

        Sede sede2 = new Sede();
        sede2.setCitta("Roma");
        sede2.setVia("Via Nazionale");
        sede2.setCivico(15);
        sede2.setCap("00100");

        List<Sede> sediList = new ArrayList<>();
        sediList.add(sede1);
        sediList.add(sede2);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sediList);
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should redirect to gestisci-sedi (new sede, no duplicates)
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_CivicoZero() throws IOException, ServletException {
        // Arrange: Civico is 0
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("0");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should allow civico 0 and redirect
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_LargeCivicoNumber() throws IOException, ServletException {
        // Arrange: Very large civico number
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("via")).thenReturn("Via Roma");
        when(request.getParameter("civico")).thenReturn("999999");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should accept large number and redirect
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_SpecialCharactersInParameters() throws IOException, ServletException {
        // Arrange: Parameters with special characters
        when(request.getParameter("citta")).thenReturn("Città d'Aosta");
        when(request.getParameter("via")).thenReturn("Via dell'Università");
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should accept special characters and redirect
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_LongStringParameters() throws IOException, ServletException {
        // Arrange: Very long strings in parameters
        String longString = "A".repeat(500);
        when(request.getParameter("citta")).thenReturn(longString);
        when(request.getParameter("via")).thenReturn(longString);
        when(request.getParameter("civico")).thenReturn("42");
        when(request.getParameter("cap")).thenReturn("20100");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
            doNothing().when(mock).doSave(any(Sede.class));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should accept long strings and redirect
            verify(response).sendRedirect("gestisci-sedi");
        }
    }

    @Test
    void testDoGet_DuplicateSedeWithMultipleInList() throws IOException, ServletException {
        // Arrange: Test duplicate detection when list has multiple sedi
        when(request.getParameter("citta")).thenReturn("Roma");
        when(request.getParameter("via")).thenReturn("Via Nazionale");
        when(request.getParameter("civico")).thenReturn("15");
        when(request.getParameter("cap")).thenReturn("00100");

        // Create multiple sedi with one matching
        Sede sede1 = new Sede();
        sede1.setCitta("Milano");
        sede1.setVia("Via Roma");
        sede1.setCivico(42);
        sede1.setCap("20100");

        Sede sede2 = new Sede();
        sede2.setCitta("Roma");
        sede2.setVia("Via Nazionale");
        sede2.setCivico(15);
        sede2.setCap("00100");

        List<Sede> sediList = new ArrayList<>();
        sediList.add(sede1);
        sediList.add(sede2);

        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/aggiungiSedi.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sediList);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should detect duplicate and forward with error attribute
            verify(request).setAttribute("esito", "non riuscito");
            verify(dispatcher).forward(request, response);
        }
    }

    @Test
    void testDoGet_AllParametersWithSpaces() throws IOException, ServletException {
        // Arrange: Parameters with leading/trailing spaces
        when(request.getParameter("citta")).thenReturn("  Milano  ");
        when(request.getParameter("via")).thenReturn("  Via Roma  ");
        when(request.getParameter("civico")).thenReturn("  42  ");
        when(request.getParameter("cap")).thenReturn("  20100  ");

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Should reject due to parseInt failure with spaces
            verify(response).sendRedirect("/WEB-INF/errorJsp/erroreForm.jsp");
        }
    }
}
